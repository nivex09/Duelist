using Facepunch;
using Facepunch.Extend;
using Network;
using Newtonsoft.Json;
using Newtonsoft.Json.Linq;
using Oxide.Core;
using Oxide.Core.Libraries.Covalence;
using Oxide.Core.Plugins;
using Oxide.Game.Rust;
using Oxide.Game.Rust.Cui;
using Oxide.Game.Rust.Libraries;
using Rust;
using Rust.Ai.Gen2;
using Rust.Workshop;
using System;
using System.Collections;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Text;
using System.Text.RegularExpressions;
using UnityEngine;
using static Oxide.Plugins.DuelistExtensionMethods.ExtensionMethods;
using Random = UnityEngine.Random;

/*
https://umod.org/community/duelist/55337-dueling-dome?page=1#post-7
https://umod.org/community/duelist/55959-dueling-ideas
https://umod.org/community/duelist/50367-the-ability-to-place-bets-in-the-economy-or-server-rewards?page=1#post-4

priority: https://umod.org/community/duelist/56195-kit-gui-on-duel-start?page=1#post-4

Fixed barricades not despawning
Fixed support for Economics
Fixed `Create New Zone Every X Duels`
Rewrote zone creation
Changed autoready to not be removed except when toggled off with /duel autoready or by clicking it in ui.
*/

namespace Oxide.Plugins
{
    [Info("Duelist", "nivex", "1.3.555")]
    [Description("1v1 and team deathmatch event.")]
    public class Duelist : RustPlugin
    {
        [PluginReference] Plugin Kits, KitController, ZoneManager, Clans, AimTrain, LustyMap;

        private const string hewwPrefab = "assets/prefabs/building/wall.external.high.wood/wall.external.high.wood.prefab";
        private const string heswPrefab = "assets/prefabs/building/wall.external.high.stone/wall.external.high.stone.prefab";
        private const bool debugMode = false;
        private const ulong DUELIST_ID = 628944326;
        private const int blockedMask = Layers.Mask.Player_Server | Layers.Mask.Construction | Layers.Mask.Deployed; // layers we won't be setting a zone within 50 meters of
        private const int constructionMask = Layers.Mask.Construction | Layers.Mask.Deployed;
        private const int groundMask = Layers.Mask.Terrain | Layers.Mask.World | Layers.Mask.Default; // used to find dueling zone/set custom zone and create spawn points
        private const int wallMask = Layers.Mask.Terrain | Layers.Mask.World | Layers.Mask.Default | Layers.Mask.Construction | Layers.Mask.Deployed;
        private const int worldMask = 8454145; 
        private bool matchUpdateRequired;
        private bool resetDuelists; // if wipe is detected then assign awards and wipe VictoriesSeed / LossesSeed
        private readonly List<BasePlayer> _emptyPlayers = new();
        private List<ulong> _times = new();
        private List<string> _suicide = new(); // users blocked from 1v1 for 60 seconds after suiciding or disconnecting
        private List<string> _disconnected = new(); // users blocked from 1v1 for 60 seconds after suiciding or disconnecting
        private List<string> readyUiList = new();
        private List<Rematch> rematches = new();
        private List<DuelingZone> duelingZones = new();
        private HashSet<string> spectators = new();
        private HashSet<GoodVersusEvilMatch> tdmMatches = new();
        private Dictionary<string, ItemDefinition> _deployables = new();
        private Dictionary<string, EscapedEventTracker> _trackers = new(); 
        private Dictionary<string, AttackerInfo> tdmAttackers = new();
        private Dictionary<string, string> tdmKits = new();
        private Dictionary<string, PlayerData> _duelists = new(); // active duelers
        private Dictionary<string, PlayerData> _immune = new(); // players immune to damage, and spawn point
        private Dictionary<string, string> announcements = new(); // users id and announcement
        private Dictionary<string, float> dataDeath = new(); // users id and timestamp of when they're to be executed
        private Dictionary<PlayerData, PlayerData> dataRequests = new(); // users requesting a duel and to whom
        private Dictionary<ulong, List<BaseEntity>> duelEntities = new();
        private Dictionary<string, DuelingZone> playerZones = new(); // id, set zone name
        private Dictionary<string, ZoneManagerInfo> ManagedZones = new(); // blocked zones from zonemanager plugin
        private Dictionary<Vector3, float> monuments = new(); // positions of monuments on the server
        private Dictionary<string, string> prefabs = new();
        private Dictionary<string, List<ulong>> skinsCache = new(); // used to randomize custom kit skins which skin id values are 0
        private Dictionary<string, string> tdmRequests = new(); // users requesting a deathmatch and to whom
        private SortedDictionary<long, PlayerData> Queued = new(); // queued duelers sorted by timestamp and user id. first come first serve
        private StoredData data = new();
        private Timer announceTimer;
        private Timer eventTimer; // timer to check for immunity and auto death time of duelers
        private Timer matchTimer; // timer to check for updates to the match ui

        // 8 flat‑plane directions: N, NE, …, NW
        private readonly Vector3[] Dir8 =
        {
            Vector3.forward, (Vector3.forward + Vector3.right).normalized,
            Vector3.right, (Vector3.right + Vector3.back).normalized,
            Vector3.back, (Vector3.back + Vector3.left).normalized,
            Vector3.left, (Vector3.left + Vector3.forward).normalized
        };

        public enum Points { MatchVictory, MatchVictorySeed, MatchLoss, MatchLossSeed, MatchDeath, MatchDeathSeed, MatchKill, MatchKillSeed, Victory, VictorySeed, Loss, LossSeed, MatchSizeVictory, MatchSizeVictorySeed, MatchSizeLoss, MatchSizeLossSeed }

        public enum Team { Good = 0, Evil = 1, None = 2 }

        public enum SelectionResult { Initiate, Full, PaymentRequired }

        public class AttackerInfo
        {
            public string AttackerName = string.Empty;
            public string AttackerId = string.Empty;
            public string BoneName = string.Empty;
            public string Distance = string.Empty;
            public string Weapon = string.Empty;
            public ItemDefinition def;
        }

        public class PlayerData : IEquatable<PlayerData>
        {
            public float Time;
            public string ID;
            public string Name;
            public Vector3 Spawn;
            public BasePlayer Player;
            public BasePlayer GetPlayer()
            {
                if (Player == null)
                {
                    using var targets = GetPlayerList();
                    foreach (var player in targets)
                    {
                        if (player.UserIDString == ID)
                        {
                            Player = player;
                            break;
                        }
                    }
                }
                return Player;
            }
            public PlayerData(BasePlayer player, float time = 0, Vector3 spawn = default)
            {
                Spawn = spawn;
                ID = player.UserIDString;
                Name = player.displayName;
                Player = player;
                Time = time;
            }
            public bool Equals(PlayerData other) => other != null && ID == other.ID;
            public override bool Equals(object obj) => obj is PlayerData data && Equals(data);
            public override int GetHashCode() => ID.GetHashCode();
        }

        public class StoredData
        {
            public List<string> Allowed = new(); // list of users that allow duel requests
            public List<string> Chat = new(); // user ids of those who opted out of seeing duel death messages
            public List<string> ChatEx = new(); // user ids of those who opted to see duel death messages when the config blocks them for all players
            public List<string> Restricted = new(); // list of users blocked from requesting a duel for 60 seconds
            public List<string> AutoReady = new(); 
            public Dictionary<string, string> Bans = new(); // users banned from dueling
            public Dictionary<string, BetInfo> Bets = new(); // active bets users have placed
            public Dictionary<string, List<string>> BlockedUsers = new(); // users and the list of players they blocked from requesting duels with
            public Dictionary<string, List<BetInfo>> ClaimBets = new(); // active bets users need to claim after winning a bet
            public Dictionary<string, string> CustomKits = new(); // userid and custom kit
            public Dictionary<string, string> Kits = new(); // userid and kit. give kit when they wake up inside of the dueling zone
            public Dictionary<string, int> MatchVictories = new(); // player name & total wins
            public Dictionary<string, int> MatchVictoriesSeed = new(); // player name & wins for current seed
            public Dictionary<string, int> MatchLosses = new(); // player name & total losses
            public Dictionary<string, int> MatchLossesSeed = new(); // player name & losses for current seed
            public Dictionary<string, int> MatchDeaths = new(); // player name & total deaths
            public Dictionary<string, int> MatchDeathsSeed = new(); // player name & deaths for the seed
            public Dictionary<string, int> MatchKills = new(); // player name & total kills
            public Dictionary<string, int> MatchKillsSeed = new(); // player name & kills for current seed
            public Dictionary<string, int> Victories = new(); // user id / wins for lifetime
            public Dictionary<string, int> VictoriesSeed = new(); // user id / wins for seed
            public Dictionary<string, int> Losses = new(); // user id / losses for lifetime
            public Dictionary<string, int> LossesSeed = new(); // user id / losses for seed
            public Dictionary<int, Dictionary<string, int>> MatchSizesVictories = new(); // size, id, wins
            public Dictionary<int, Dictionary<string, int>> MatchSizesVictoriesSeed = new(); // size, id, wins seed
            public Dictionary<int, Dictionary<string, int>> MatchSizesLosses = new(); // size, id, losses
            public Dictionary<int, Dictionary<string, int>> MatchSizesLossesSeed = new(); // size, id, losses seed

            [JsonConverter(typeof(UnityVector3Converter))]
            public List<Vector3> Spawns = new(); // custom spawn points

            [JsonConverter(typeof(UnityVector3Converter))]
            public Dictionary<Vector3, List<Vector3>> AutoGeneratedSpawns = new();

            [JsonConverter(typeof(UnityVector3Converter))]
            public Dictionary<string, Vector3> Homes = new(); // user id and location of where they teleported from

            [JsonConverter(typeof(UnityVector3Converter))]
            public Dictionary<Vector3, DuelZoneInfo> Zones = new(); // location, name

            public bool DuelsEnabled; // enable/disable dueling for all players (not admins)
            public int TotalDuels; // the total amount of duels ever played on the server

            public int Add(string userid, Points points, int matchSize)
            {
                if (!userid.IsSteamId())
                    return 1;

                Dictionary<int, Dictionary<string, int>> dict = GetSize(points);

                Dictionary<string, int> inner = dict.GetOrCreate(matchSize);

                return inner[userid] = inner.GetOrCreate(userid) + 1;
            }

            public int Add(string userid, Points points)
            {
                if (!userid.IsSteamId())
                    return 1;

                Dictionary<string, int> dict = points switch
                {
                    Points.MatchVictory => MatchVictories,
                    Points.MatchVictorySeed => MatchVictoriesSeed,
                    Points.MatchLoss => MatchLosses,
                    Points.MatchLossSeed => MatchLossesSeed,
                    Points.MatchDeath => MatchDeaths,
                    Points.MatchDeathSeed => MatchDeathsSeed,
                    Points.MatchKill => MatchKills,
                    Points.MatchKillSeed => MatchKillsSeed,
                    Points.Victory => Victories,
                    Points.VictorySeed => VictoriesSeed,
                    Points.Loss => Losses,
                    Points.LossSeed or _ => LossesSeed
                };

                return dict[userid] = dict.GetOrCreate(userid) + 1;
            }

            public Dictionary<string, int> Get(Points points)
            {
                return points switch
                {
                    Points.MatchVictory => MatchVictories,
                    Points.MatchVictorySeed => MatchVictoriesSeed,
                    Points.MatchLoss => MatchLosses,
                    Points.MatchLossSeed => MatchLossesSeed,
                    Points.MatchDeath => MatchDeaths,
                    Points.MatchDeathSeed => MatchDeathsSeed,
                    Points.MatchKill => MatchKills,
                    Points.MatchKillSeed => MatchKillsSeed,
                    Points.Victory => Victories,
                    Points.VictorySeed => VictoriesSeed,
                    Points.Loss => Losses,
                    Points.LossSeed or _ => LossesSeed,
                };
            }

            public Dictionary<int, Dictionary<string, int>> GetSize(Points points)
            {
                return points switch
                {
                    Points.MatchSizeVictory => MatchSizesVictories,
                    Points.MatchSizeVictorySeed => MatchSizesVictoriesSeed,
                    Points.MatchSizeLoss => MatchSizesLosses,
                    Points.MatchSizeLossSeed or _ => MatchSizesLossesSeed,
                };
            }

            public int Get(string userid, Points points)
            {
                if (!userid.IsSteamId())
                    return UnityEngine.Random.Range(0, 16);

                return Get(points).TryGetValue(userid, out int value) ? value : 0;
            }

            public int Get(string userid, Points points, int matchSize)
            {
                if (!userid.IsSteamId())
                    return 0;

                Dictionary<int, Dictionary<string, int>> dict = GetSize(points);

                if (!dict.TryGetValue(matchSize, out var inner))
                    return 0;

                return inner.TryGetValue(userid, out int value) ? value : 0;
            }

            public void ResetSeed()
            {
                LossesSeed.Clear();
                VictoriesSeed.Clear();
                MatchKillsSeed.Clear();
                MatchDeathsSeed.Clear();
                MatchLossesSeed.Clear();
                MatchVictoriesSeed.Clear();
                MatchSizesVictoriesSeed.Clear();
                MatchSizesLossesSeed.Clear();
            }
        }

        public class UnityVector3Converter : JsonConverter
        {
            private static string FormatS(Vector3 v)
            {
                return FormattableString.Invariant($"{v.x:0.###} {v.y:0.###} {v.z:0.###}");
            }

            private static string Format(Vector3 v)
            {
                return FormattableString.Invariant($"{v.x:R} {v.y:R} {v.z:R}");
            }

            private static Vector3 Parse(string s)
            {
                var parts = s.Split(' ', StringSplitOptions.RemoveEmptyEntries);
                return new(Convert.ToSingle(parts[0], CultureInfo.InvariantCulture), Convert.ToSingle(parts[1], CultureInfo.InvariantCulture), Convert.ToSingle(parts[2], CultureInfo.InvariantCulture));
            }

            private static Vector3 Parse(JObject o)
            {
                return new(Convert.ToSingle(o["x"], CultureInfo.InvariantCulture), Convert.ToSingle(o["y"], CultureInfo.InvariantCulture), Convert.ToSingle(o["z"], CultureInfo.InvariantCulture));
            }

            public override bool CanConvert(Type objectType)
            {
                return objectType == typeof(Vector3)
                    || objectType == typeof(List<Vector3>)
                    || objectType == typeof(Dictionary<string, Vector3>)
                    || objectType == typeof(Dictionary<string, List<Vector3>>)
                    || objectType == typeof(Dictionary<string, DuelZoneInfo>)
                    || objectType == typeof(Dictionary<Vector3, DuelZoneInfo>)
                    || objectType == typeof(Dictionary<Vector3, List<Vector3>>);
            }

            public override void WriteJson(JsonWriter writer, object value, JsonSerializer serializer)
            {
                if (value is Vector3 v)
                {
                    if (!v.IsNaNOrInfinity())
                    {
                        writer.WriteValue(Format(v));
                    }
                    return;
                }

                if (value is IEnumerable<Vector3> vecList)
                {
                    writer.WriteStartArray();
                    foreach (var vec in vecList)
                    {
                        if (vec.IsNaNOrInfinity()) continue;
                        writer.WriteValue(Format(vec));
                    }
                    writer.WriteEndArray();
                    return;
                }

                if (value is IDictionary dict)
                {
                    writer.WriteStartObject();
                    var written = new HashSet<string>();
                    foreach (DictionaryEntry entry in dict)
                    {
                        string key = entry.Key is Vector3 kv ? Format(kv) : entry.Key.ToString();
                        if (!written.Add(key)) continue;
                        writer.WritePropertyName(key);
                        serializer.Serialize(writer, entry.Value);
                    }
                    writer.WriteEndObject();
                }
            }

            public override object ReadJson(JsonReader reader, Type objectType, object existingValue, JsonSerializer serializer)
            {
                if (objectType == typeof(Vector3))
                {
                    return reader.TokenType switch
                    {
                        JsonToken.String => Parse((string)reader.Value),
                        JsonToken.StartObject => Parse(JObject.Load(reader)),
                        _ => throw new JsonSerializationException($"Unexpected token '{reader.TokenType}' when parsing Vector3.")
                    };
                }

                if (objectType == typeof(List<Vector3>))
                {
                    var list = new List<Vector3>();
                    if (reader.TokenType != JsonToken.StartArray)
                    {
                        throw new JsonSerializationException($"Unexpected token '{reader.TokenType}' when parsing List<Vector3>.");
                    }
                    while (reader.Read() && reader.TokenType != JsonToken.EndArray)
                    {
                        if (reader.TokenType == JsonToken.String)
                        {
                            list.Add(Parse((string)reader.Value));
                        }
                        else if (reader.TokenType == JsonToken.StartObject)
                        {
                            list.Add(Parse(JObject.Load(reader)));
                        }
                        else
                        {
                            throw new JsonSerializationException($"Unexpected token '{reader.TokenType}' inside List<Vector3>.");
                        }
                    }
                    return list;
                }

                if (objectType == typeof(Dictionary<string, List<Vector3>>))
                {
                    var dict = new Dictionary<string, List<Vector3>>();
                    var obj = JObject.Load(reader);
                    foreach (var prop in obj.Properties())
                    {
                        var list = new List<Vector3>();
                        foreach (var token in (JArray)prop.Value)
                        {
                            list.Add(token.Type == JTokenType.String ? Parse(token.ToString()) : Parse((JObject)token));
                        }
                        dict[prop.Name] = list;
                    }
                    return dict;
                }

                if (objectType == typeof(Dictionary<Vector3, List<Vector3>>))
                {
                    var dict = new Dictionary<Vector3, List<Vector3>>();
                    var obj = JObject.Load(reader);
                    foreach (var prop in obj.Properties())
                    {
                        var key = Parse(prop.Name);
                        var list = new List<Vector3>();
                        foreach (var token in (JArray)prop.Value)
                        {
                            list.Add(token.Type == JTokenType.String ? Parse(token.ToString()) : Parse((JObject)token));
                        }
                        dict[key] = list;
                    }
                    return dict;
                }

                if (objectType == typeof(Dictionary<string, Vector3>))
                {
                    var dict = new Dictionary<string, Vector3>();
                    var obj = JObject.Load(reader);
                    foreach (var prop in obj.Properties())
                    {
                        dict[prop.Name] = prop.Value.Type == JTokenType.String ? Parse(prop.Value.ToString()) : Parse((JObject)prop.Value);
                    }
                    return dict;
                }

                if (objectType == typeof(Dictionary<Vector3, DuelZoneInfo>))
                {
                    var dict = new Dictionary<Vector3, DuelZoneInfo>();
                    var obj = JObject.Load(reader);
                    foreach (var prop in obj.Properties())
                    {
                        var key = Parse(prop.Name);
                        dict[key] = prop.Value.ToObject<DuelZoneInfo>(serializer);
                    }
                    return dict;
                }

                throw new JsonSerializationException($"Unsupported object type '{objectType}' for UnityVector3Converter.");
            }
        }

        public class ZoneManagerInfo
        {
            internal string ZoneId;
            internal Quaternion Rotation;
            internal Vector3 Position;
            internal Vector3 Size;
            internal Vector3 extents;
            internal float Distance;
            internal bool IsBlocked;
            internal const float M_RADIUS = 25f;

            public ZoneManagerInfo(string id, Vector3 pos, Quaternion rot, float radius, Vector3 size, bool isBlocked, float dist)
            {
                (IsBlocked, ZoneId, Position, Rotation) = (isBlocked, id, pos, rot);

                dist = Mathf.Max(dist, 100f);
                Distance = radius + M_RADIUS + dist;

                if (size != Vector3.zero)
                {
                    Size = size + new Vector3(dist, Position.y + 100f, dist);
                    extents = Size * 0.5f;
                }
            }

            public bool IsPositionInZone(Vector3 a)
            {
                if (Size != Vector3.zero)
                {
                    Vector3 v = Quaternion.Inverse(Rotation) * (a - Position);

                    return v.x <= extents.x && v.x > -extents.x && v.y <= extents.y && v.y > -extents.y && v.z <= extents.z && v.z > -extents.z;
                }
                return InRange2D(Position, a, Distance);
            }
        }

        public class DuelZoneInfo
        {
            public string name;
            public float radius;
            public DuelZoneInfo() { }
            public DuelZoneInfo(string name, float radius)
            {
                this.name = name;
                this.radius = Mathf.Clamp(radius, 50f, 300f);
            }
        }

        private class EscapedEventTracker : FacepunchBehaviour
        {
            internal BasePlayer player;
            internal Duelist env;
            internal bool isDestroyed;
            internal bool duel;
            internal ulong id;

            public void Init(BasePlayer player, Duelist env, bool duel)
            {
                id = player.userID;
                this.player = player;
                this.env = env;
                InvokeRepeating(Track, 0f, 0.5f);
            }

            private void Track()
            {
                if (isDestroyed) 
                    return;

                if (player == null || player.IsDestroyed)
                {
                    env.RemoveEntities(id);
                    DestroyMe();
                    return;
                }

                if (duel ? !env.IsDuelist(player.UserIDString) : !env.IsTeamMember(player.UserIDString))
                {
                    return;
                }

                if (!env.DuelTerritory(player.transform.position))
                {
                    player.inventory.Strip();
                    DestroyMe();
                }
            }

            public void DestroyMe()
            {
                isDestroyed = true;
                Destroy(this);
            }
        }

        public static PooledList<T> GetPooledList<T>(IEnumerable<T> e1 = null, IEnumerable<T> e2 = null)
        {
            var pool = Pool.Get<PooledList<T>>();
            if (e1 != null) pool.AddRange(e1);
            if (e2 != null) pool.AddRange(e2);
            return pool;
        }

        public class Rematch
        {
            public Rematch(Duelist env)
            {
                this.env = env;
            }
            private Duelist env;
            public List<BasePlayer> Duelists = new();
            public List<BasePlayer> Ready = new();
            private List<BasePlayer> Evil = new();
            private List<BasePlayer> Good = new();
            public GoodVersusEvilMatch match;
            private Timer _notify;

            public PooledList<BasePlayer> GetAllPlayers()
            {
                Duelists.RemoveAll(IsNotConnected);
                Good.RemoveAll(IsNotConnected);
                Evil.RemoveAll(IsNotConnected);
                Ready.RemoveAll(IsNotConnected);

                if (match == null)
                {
                    return GetPooledList(Duelists);
                }

                return GetPooledList(Good, Evil);
            }

            public bool HasPlayer(BasePlayer player)
            {
                if (match == null)
                {
                    return Duelists.Contains(player);
                }
                return Good.Contains(player) || Evil.Contains(player);
            }

            public bool AddRange(Dictionary<string, BasePlayer> players, Team team)
            {
                foreach (var player in players.Values)
                {
                    if (env.IsParticipant(player))
                        return false;

                    GetTeam(team).Add(player);
                }

                return true;
            }

            public List<BasePlayer> GetTeam(Team team)
            {
                return team == Team.Evil ? Evil : Good;
            }

            public bool IsReady(BasePlayer player)
            {
                return !env.IsParticipant(player) && env.IsNewman(player) && !env.data.Bans.ContainsKey(player.UserIDString);
            }

            public bool IsReady()
            {
                using var players = GetAllPlayers();
                if (players.Exists(player => !IsReady(player)))
                {
                    Reset("RematchFailed2");
                    return false;
                }

                return Ready.Count == (match == null ? 2 : match.TeamSize * 2);
            }

            private void Reset(string key = null)
            {
                env.tdmMatches.Remove(match);
                if (key != null) MessageAll(key);
                Duelists.Clear();
                Good.Clear();
                Evil.Clear();
                Ready.Clear();
                _notify?.Destroy();
                env.rematches.Remove(this);
                env.matchUpdateRequired = true;
            }

            public void MessageAll(string key, params object[] args)
            {
                using var players = GetAllPlayers();
                foreach (var player in players)
                {
                    env.Message(player, key, args);
                }
            }

            public void ReadyCheck()
            {
                using var players = GetAllPlayers();
                foreach (var player in players)
                {
                    if (env.autoReady || env.data.AutoReady.Contains(player.UserIDString))
                    {
                        Ready.Add(player);
                    }
                    else env.Message(player, "RematchNotify", 60f, match == null ? env.szDuelChatCommand : env.szMatchChatCommand);
                }

                if (IsReady())
                {
                    Start();
                    env.rematches.Remove(this);
                }
                else if (match == null || !match.IsPublic)
                    _notify = env.timer.Once(60f, Cancel);
            }

            public void Start()
            {
                if (match == null)
                {
                    var player = Ready[0];
                    var target = Ready[1];

                    if (!env.SelectZone(player, target, false))
                    {
                        env.Message(player, "AllZonesFull", env.duelingZones.Count, env.playersPerZone);
                        env.Message(target, "AllZonesFull", env.duelingZones.Count, env.playersPerZone);
                    }
                }
                else
                {
                    match.Reuse(false);
                    env.tdmMatches.Add(match);

                    if (!AddMatchPlayers(Good, Team.Good) || !AddMatchPlayers(Evil, Team.Evil))
                    {
                        Reset("RematchFailed");
                        match.Reuse(true);
                    }
                }

                _notify?.Destroy();
                env.rematches.Remove(this);
            }

            private void Cancel()
            {
                if (match != null && match.IsPublic)
                    return;

                if (env.rematches.Contains(this))
                    return;

                if (env.sendHomeSpectatorWhenRematchTimesOut)
                {
                    using var players = GetAllPlayers();
                    foreach (var player in players)
                    {
                        if (player is DuelistNPC)
                        {
                            player.DelayedSafeKill();
                            continue;
                        }
                        if (env.IsSpectating(player))
                        {
                            env.EndSpectate(player);
                            env.SendHome(player);
                        }
                    }
                }

                if (match != null)
                {
                    match.Reuse(true);
                }

                Reset("RematchTimedOut");
            }

            private bool AddMatchPlayers(List<BasePlayer> players, Team team)
            {
                foreach (var player in players)
                    if (!match.AddMatchPlayer(player, team))
                        return false;

                return true;
            }
        }

        public class GoodVersusEvilMatch
        {
            public class Host
            {
                public int RoundsWon;
                public string ID = string.Empty;
                public string Name = string.Empty;
                public string Code = string.Empty;
                public HashSet<string> KIA = new();
                public Dictionary<string, BasePlayer> Rematch = new();
                public Dictionary<string, BasePlayer> Players = new();
                public void SetNewHostId()
                {
                    foreach (var player in Players.Values)
                    {
                        if (player != null)
                        {
                            ID = player.UserIDString;
                            return;
                        }
                    }
                    ID = string.Empty;
                }
                public bool CanRematch() => Rematch.Count > 0 && !Rematch.Values.Exists(IsNotConnected);
            }
            
            public GoodVersusEvilMatch(Duelist env)
            {
                this.env = env;
                TotalRounds = env.config.Deathmatch.Rounds;
            }

            public bool Equals(GoodVersusEvilMatch match) => match.Id == Id;

            public string Id { get; } = Guid.NewGuid().ToString();
            private Duelist env;
            private HashSet<ulong> _banned = new();
            private HashSet<ulong> IsLocked = new();
            private Timer _queueTimer;
            private DuelingZone _zone;
            internal Host Good = new();
            internal Host Evil = new();
            private int _teamSize = 2;
            private bool _started;
            private bool _ended;
            private bool _queued;
            private bool _public;
            public bool CanRematch = true;
            private string _kit = string.Empty;

            public string Versus => string.Format("{0} / {1} {2}v{2}", Good.Name, Evil.Name, _teamSize);

            public int RoundIndex; // 0‑based counter
            public int TotalRounds = 3;
            public Dictionary<string, int> RoundsLeft = new(); // userid + rounds left
            
            private void InitRounds()
            {
                RoundsLeft.Clear();
                foreach (var id in Good.Players.Keys)
                {
                    RoundsLeft[id] = TotalRounds;
                }
                foreach (var id in Evil.Players.Keys)
                {
                    RoundsLeft[id] = TotalRounds;
                }
            }

            private void DecrementRounds()
            {
                using var keys = GetPooledList<string>();
                keys.AddRange(RoundsLeft.Keys);
                foreach (var id in keys)
                {
                    if (--RoundsLeft[id] <= 0)
                    {
                        RoundsLeft.Remove(id);
                    }
                }
            }

            private void ResetRounds()
            {
                RoundIndex = 0;
                Good.RoundsWon = 0;
                Evil.RoundsWon = 0;
                Good.Players.Clear();
                Evil.Players.Clear();
            }

            public int RoundsCompleted() => Good.RoundsWon + Evil.RoundsWon;

            public bool HasRoundsLeft(string userid) => RoundsLeft.TryGetValue(userid, out int value) && value > 0;

            public bool SendDefeatedHome(string userid) => env.sendDefeatedHome && !HasRoundsLeft(userid);

            public bool IsPublic
            {
                get => _public;
                set
                {
                    _public = value;
                    env.matchUpdateRequired = true;
                    MessageAll(_public ? "MatchPublic" : "MatchPrivate");
                }
            }

            public int TeamSize
            {
                get => _teamSize;
                set
                {
                    if (IsStarted)
                        return;

                    _teamSize = value;
                    env.matchUpdateRequired = true;
                    MessageAll("MatchSizeChanged", _teamSize);
                }
            }

            public DuelingZone Zone => _zone;

            public bool EitherEmpty => Good.Players.Count == 0 || Evil.Players.Count == 0;

            public bool IsStarted
            {
                get => _started;
                set
                {
                    _started = value;
                    env.matchUpdateRequired = true;
                }
            }

            public bool IsOver
            {
                get => _ended;
                set
                {
                    _ended = value;
                    env.matchUpdateRequired = true;
                }
            }

            public string Kit
            {
                get => _kit;
                set
                {
                    _kit = value;

                    if (!EitherEmpty)
                    {
                        SetPlayerKit(Good);
                        SetPlayerKit(Evil);
                    }
                }
            }

            private void SetPlayerKit(Host host)
            {
                foreach (var user in host.Players)
                {
                    if (user.Value != null)
                    {
                        env.data.Kits[user.Key] = _kit;
                        Message(user.Value, "MatchKitSet", _kit);
                    }
                    else env.data.Kits.Remove(user.Key);
                }
            }

            public void Reuse(bool kia)
            {
                if (_zone != null)
                    _zone.IsLocked = false;

                if (kia)
                {
                    Evil.KIA.Clear();
                    Good.KIA.Clear();
                }

                Evil.Rematch.Clear();
                Evil.Players.Clear();
                Good.Rematch.Clear();
                Good.Players.Clear();
                _started = false;
                _ended = false;
                _queued = false;
                _kit = env.GetRandomKit();
                env.matchUpdateRequired = true;
            }

            public void Setup(BasePlayer player, BasePlayer target)
            {
                env.tdmMatches.Add(this);
                Good.Name = player.displayName;
                Good.ID = player.UserIDString;
                Evil.Name = target.displayName;
                Evil.ID = target.UserIDString;
                Good.Code = Random.Range(10000, 99999).ToString();
                Evil.Code = Random.Range(10000, 99999).ToString();

                if (_teamSize < env.minDeathmatchSize)
                    _teamSize = env.minDeathmatchSize;

                AddMatchPlayer(player, Team.Good);
                AddMatchPlayer(target, Team.Evil);

                if (env.tdmKits.Remove(player.UserIDString, out var kit) || env.tdmKits.Remove(target.UserIDString, out kit))
                {
                    Kit = kit;
                }
                else Kit = env.GetRandomKit();

                if (TeamSize > 1)
                {
                    Message(player, "MatchOpened", env.szMatchChatCommand, Good.Code);
                    Message(target, "MatchOpened", env.szMatchChatCommand, Evil.Code);
                }

                env.matchUpdateRequired = true;
            }
            
            public bool IsAlliedTo(BasePlayer player, Team team) => env.IsAllied(player.UserIDString, GetHost(team).ID);
            
            public bool IsHost(BasePlayer player) => player.UserIDString == Good.ID || player.UserIDString == Evil.ID;

            public bool IsHost(BasePlayer player, out Host host)
            {
                if (player.UserIDString == Good.ID)
                {
                    host = Good;
                    return true;
                }
                if (player.UserIDString == Evil.ID)
                {
                    host = Evil;
                    return true;
                }
                host = null;
                return false;
            }

            public bool IsFull() => Good.Players.Count >= _teamSize && Evil.Players.Count >= _teamSize;
            
            public bool IsFull(Team team) => GetHost(team).Players.Count >= _teamSize;

            public string GetCode(Team team) => team == Team.Good ? Good.Code : Evil.Code;

            public string GetCode(Host host) => host.Code;

            public void SetCode(Host host, string code) => host.Code = code;
            
            public void SetCode(Team team, string code) => GetHost(team).Code = code;

            public Host GetHost(Team team) => team == Team.Good ? Good : Evil;

            public Host GetOpposingHost(Team team) => team == Team.Good ? Evil : Good;

            public string GetHostName(Team team) => team == Team.Good ? Good.Name : Evil.Name;

            public string GetOpposingName(Team team) => team == Team.Good ? Evil.Name : Good.Name;

            public IEnumerable<BasePlayer> GetTeamMembers(Team team) => GetHost(team).Players.Values;

            public Team GetTeam(BasePlayer player) => player == null ? Team.None : GetTeam(player.UserIDString);

            public Team GetTeam(string userid) => Good.Players.ContainsKey(userid) ? Team.Good : Evil.Players.ContainsKey(userid) ? Team.Evil : Team.None;

            public string GetTeamNames(Team team)
            {
                using var sb = DisposableBuilder.Get();
                foreach (var player in GetTeamMembers(team))
                {
                    if (player != null)
                    {
                        sb.Append(player.displayName).Append(", ");
                    }
                }
                if (sb.Length > 0)
                {
                    sb.Length -= 2;
                    return sb.ToString();
                }
                return string.Empty;
            }

            public bool IsBanned(ulong targetId) => _banned.Contains(targetId);

            public bool Ban(BasePlayer target)
            {
                if (IsHost(target) || IsBanned(target.userID))
                    return false;

                _banned.Add(target.userID);
                RoundsLeft.Remove(target.UserIDString);
                RemoveMatchPlayer(target);
                return true;
            }

            public void MessageAll(string key, params object[] args)
            {
                Message(Good.Players.Values, key, args);
                Message(Evil.Players.Values, key, args);
            }

            private void Message(BasePlayer player, string key, params object[] args) => env.Message(player, key, args);

            private void Message(IEnumerable<BasePlayer> players, string key, params object[] args) => env.MessageAll(players, key, args);

            public void GiveShirt(BasePlayer player)
            {
                var team = GetTeam(player);
                var shirtName = env.teamShirt;
                var fallbackSkin = team == Team.Evil ? 14177UL : 101UL;
                var teamSkin = team == Team.Evil ? env.teamEvilShirt : env.teamGoodShirt;
                var def = ItemManager.FindItemDefinition(shirtName);

                if (def != null && env.RequiresOwnership(def, teamSkin)) 
                    teamSkin = fallbackSkin;

                if (IsLocked.Add(player.userID))
                    player.inventory.containerWear.SetLocked(true);

                foreach (Item wear in player.inventory.containerWear.itemList)
                {
                    if (wear.info.shortname == shirtName)
                    {
                        wear.skin = teamSkin;
                        wear.MarkDirty();
                        return;
                    }
                    if (wear.info.shortname.Contains("hoodie") || wear.info.shortname.Contains("shirt"))
                    {
                        wear.RemoveFromContainer();
                        wear.Remove(0.01f);
                        break;
                    }
                }

                if (def == null || def.category != ItemCategory.Attire)
                    return;

                var skin = ItemDefinition.FindSkin(def.itemid, (int)teamSkin);
                var item = skin != teamSkin ? ItemManager.CreateByName("tshirt", 1, fallbackSkin) : ItemManager.Create(def, 1, skin);
                if (item != null && !item.MoveToContainer(player.inventory.containerWear))
                    item.Remove();
            }

            public bool AddMatchPlayer(BasePlayer player, Team team)
            {
                if (IsStarted)
                {
                    Message(player, "MatchStartedAlready");
                    return false;
                }

                Good.Players.RemoveWhere(IsNotConnected);
                Evil.Players.RemoveWhere(IsNotConnected);

                if (IsBanned(player.userID))
                    return false;

                if (!env.IsNewman(player))
                {
                    Message(player, "MustBeNaked");
                    return false;
                }

                var host = GetHost(team);
                var opponent = GetOpposingHost(team);

                if (host.Players.Count >= _teamSize)
                {
                    Message(player, "MatchTeamFull", _teamSize);
                    return false;
                }

                RoundsLeft.TryAdd(player.UserIDString, TotalRounds);
                host.Players[player.UserIDString] = player;

                if (RoundIndex == 0)
                {
                    MessageAll("MatchJoinedTeam", player.displayName, host.Name, host.Players.Count, _teamSize, opponent.Name, opponent.Players.Count);
                }

                if (IsFull())
                {
                    Queue();
                }

                return true;
            }

            public bool RemoveMatchPlayer(BasePlayer player)
            {
                if (player == null)
                    return false;

                if (IsLocked.Remove(player.userID))
                    player.inventory.containerWear.SetLocked(false);

                env.Metabolize(player, false);
                env.SetEscapedEventTracker(player, false, false);
                env.RemoveEntities(player.userID);
                Interface.Oxide.CallHook("DisableBypass", (ulong)player.userID);

                if (!HasRoundsLeft(player.UserIDString) && env.DuelTerritory(player.transform.position))
                {
                    if (SendDefeatedHome(player.UserIDString))
                    {
                        if (player is DuelistNPC)
                        {
                            player.DelayedSafeKill();
                        }
                        else env.SendHome(player);
                    }
                    else //if (!IsOver)
                    {
                        env.StartSpectate(player);
                    }
                }

                if (IsOver)
                {
                    Good.Players.Remove(player.UserIDString);
                    Evil.Players.Remove(player.UserIDString);
                    return true;
                }

                return RemoveMatchPlayer(player, Team.Good) || RemoveMatchPlayer(player, Team.Evil);
            }

            private bool RemoveMatchPlayer(BasePlayer player, Team team)
            {
                Host host = GetHost(team);
                if (!host.Players.Remove(player.UserIDString))
                    return false;
                
                if (host.Players.Count == 0)
                {
                    if (_started)
                    {
                        host.KIA.Add(player.UserIDString);
                        host.Rematch[player.UserIDString] = player;
                    }
                    else MessageAll("MatchNoPlayersLeft");

                    EndMatch(team == Team.Evil ? Team.Good : Team.Evil);
                    return true;
                }

                if (_started)
                {
                    host.KIA.Add(player.UserIDString);
                    host.Rematch[player.UserIDString] = player;
                }

                if (player.UserIDString == host.ID)
                    AssignHostId(host, team);

                return true;
            }

            private void AssignHostId(Host host, Team team)
            {
                host.Players.RemoveWhere(IsNotConnected);

                if (host.Players.Count > 0)
                {
                    host.SetNewHostId();
                    env.matchUpdateRequired = true;
                }
                else EndMatch(team);
            }

            private void Finalize(Team team)
            {
                Host victor = GetHost(team);
                Host loser = GetOpposingHost(team);

                victor.KIA.UnionWith(victor.Rematch.Keys);
                loser.KIA.UnionWith(loser.Rematch.Keys);
                
                Interface.CallHook("OnDuelistFinalized", victor.KIA);

                UpdateSide(loser.KIA, Points.MatchLoss);
                UpdateSide(victor.KIA, Points.MatchVictory);

                Good.KIA.Clear();
                Evil.KIA.Clear();
            }
            
            private void UpdateSide(IEnumerable<string> ids, Points stat)
            {
                foreach (var id in ids)
                {
                    if (stat == Points.MatchVictory)
                        env.AwardPlayer(id, env.teamEconomicsMoney, env.teamServerRewardsPoints);

                    env.UpdateMatchStats(id, stat);
                    env.UpdateMatchSizeStats(id, _teamSize, stat);
                }
            }

            private bool SetupRematch()
            {
                if (!CanRematch || !Good.CanRematch() || !Evil.CanRematch())
                    return false;

                Rematch rematch = new(env);
                if (rematch.AddRange(Evil.Rematch, Team.Evil) && rematch.AddRange(Good.Rematch, Team.Good))
                {
                    env.rematches.Add(rematch);
                    rematch.match = this;
                    rematch.ReadyCheck();
                    return true;
                }

                return false;
            }

            public void EndMatch(Team team)
            {
                if (!_ended && _started)
                {
                    DecrementRounds(); // burn a round for everyone
                    IsOver = true;
                    IsStarted = false;
                    _queued = false;

                    using var evil = GetPooledList(Evil.Players.Values);

                    foreach (var player in evil)
                    {
                        RemoveMatchPlayer(player);

                        if (IsConnected(player) && !Evil.Rematch.ContainsKey(player.UserIDString))
                        {
                            Evil.Rematch[player.UserIDString] = player;
                            player.inventory.Strip();
                        }
                    }

                    using var good = GetPooledList(Good.Players.Values);

                    foreach (var player in good)
                    {
                        RemoveMatchPlayer(player);

                        if (IsConnected(player) && !Good.Rematch.ContainsKey(player.UserIDString))
                        {
                            Good.Rematch[player.UserIDString] = player;
                            player.inventory.Strip();
                        }
                    }

                    // more rounds left?
                    GetHost(team).RoundsWon += 1;
                    if (TotalRounds > 1 && RoundIndex < TotalRounds && CanRematch && Good.CanRematch() && Evil.CanRematch())
                    {
                        _started = false;
                        _ended = false;

                        Rematch rematch = new(env);
                        if (rematch.AddRange(Evil.Rematch, Team.Evil) && rematch.AddRange(Good.Rematch, Team.Good))
                        {
                            Good.KIA.Clear();
                            Evil.KIA.Clear();
                            env.rematches.Add(rematch);
                            rematch.match = this;
                            rematch.Start();
                            return;
                        }
                    }

                    int rounds = RoundsCompleted();
                    team = Good.RoundsWon > Evil.RoundsWon ? Team.Good : Team.Evil;

                    Puts(env.msg("MatchDefeat", null, GetHostName(team), GetOpposingName(team), _teamSize));

                    using var targets = GetPlayerList();
                    foreach (var target in targets)
                    {
                        if (env.guiAnnounceUITime > 0f && (Good.KIA.Contains(target.UserIDString) || Evil.KIA.Contains(target.UserIDString)))
                            env.CreateAnnouncementUI(target, env.msg("MatchDefeat", target.UserIDString, GetHostName(team), GetOpposingName(team), _teamSize));

                        if (!IsChatEnabled(target.UserIDString))
                            continue;

                        Message(target, "MatchDefeat", GetHostName(team), GetOpposingName(team), _teamSize);
                    }

                    Finalize(team);
                    Good.RoundsWon = 0;
                    Evil.RoundsWon = 0;

                    if (TotalRounds > 1 && rounds >= TotalRounds)
                    {
                        End(true);
                        TryRelocateZone();
                        return;
                    }

                    if (TotalRounds <= 1)
                    {
                        TryRelocateZone();
                    }

                    if (SetupRematch())
                    {
                        return;
                    }

                    using var players = GetPooledList(Evil.Rematch.Values, Good.Rematch.Values);

                    foreach (var player in players)
                    {
                        if (IsNotConnected(player)) continue;
                        Message(player, "RematchFailed2");
                    }

                    Reuse(true);
                }

                End();
            }

            // if it's time to relocate the zone then lock the zone so it cannot be used again. attempt to relocate if not occupied
            public void TryRelocateZone()
            {
                if (_zone != null && !_zone.IsFinito)
                {
                    env.TryRelocateZone(_zone);
                }
            }

            public bool IsChatEnabled(string userid) => !env.data.Chat.Contains(userid) || Good.KIA.Contains(userid) || Evil.KIA.Contains(userid);

            public void End(bool defeat = false)
            {
                if (_zone != null)
                    _zone.IsLocked = false;

                _queueTimer?.Destroy();

                using var players = GetAllPlayers();

                foreach (var player in players)
                {
                    if (IsLocked.Remove(player.userID))
                        player.inventory.containerWear.SetLocked(false);

                    if (IsStarted || IsOver)
                    {
                        env.Reappear(player);
                        if (env.DuelTerritory(player.transform.position))
                        {
                            player.inventory.Strip();
                            if (player is DuelistNPC)
                            {
                                player.DelayedSafeKill();
                            }
                            else if (!defeat || SendDefeatedHome(player.UserIDString))
                            {
                                env.SendHome(player);
                            }
                        }

                        env.Metabolize(player, false);
                        env.SetEscapedEventTracker(player, false, false);
                    }
                }

                ResetRounds();
                env.tdmMatches.Remove(this);
                env.matchUpdateRequired = true;

                if (!env.AnyParticipants())
                    env.Unsubscribe(nameof(OnPlayerHealthChange));
            }

            private float nextNakedMessageTime;

            private void Queue()
            {
                DuelingZone teamZone = null;
                DuelingZone spatialZone = null;

                using var players = GetAllPlayers();

                int needed = env.requireTeamSize ? TeamSize * 2 : 2;

                foreach (var player in players)
                {
                    if (!env.IsNewman(player))
                    {
                        if (Time.time > nextNakedMessageTime)
                        {
                            nextNakedMessageTime = Time.time + 30f;
                            MessageAll("MatchIsNotNaked", player.displayName);
                        }
                        Message(player, "MustBeNaked");
                        _queueTimer = env.timer.Once(2f, Queue);
                        return;
                    }

                    teamZone ??= env.GetPlayerZone(player, TeamSize);

                    if (spatialZone == null)
                    {
                        var z = env.GetDuelZone(player.transform.position);
                        if (IsZoneEmpty(z, needed))
                            spatialZone = z;
                    }
                }

                _zone = teamZone ?? spatialZone ?? FindGlobalZone(needed);

                if (_zone == null)
                {
                    if (!_queued)
                    {
                        MessageAll("MatchQueued");
                        _queued = true;
                    }
                    _queueTimer = env.timer.Once(2f, Queue);
                }
                else
                {
                    _queueTimer?.Destroy();
                    //_enteredQueue = false;
                    Start();
                }
            }

            private DuelingZone FindGlobalZone(int needed)
            {
                using var zones = GetPooledList<DuelingZone>();
                foreach (var z in env.duelingZones)
                {
                    if (IsZoneEmpty(z, needed)) zones.Add(z);
                }
                return zones.Count > 0 ? zones.GetRandom() : null;
            }

            public PooledList<BasePlayer> GetAllPlayers()
            {
                var players = GetPooledList<BasePlayer>();
                foreach (var good in Good.Players.Values)
                {
                    if (IsConnected(good)) players.Add(good);
                }
                foreach (var evil in Evil.Players.Values)
                {
                    if (IsConnected(evil)) players.Add(evil);
                }
                return players;
            }

            private void Start()
            {
                if (RoundIndex == 0)
                    InitRounds();
                RoundIndex++;

                Vector3 goodSpawn = _zone.Spawns.GetRandom();
                Vector3 evilSpawn = goodSpawn;
                float maxSqr = float.MinValue;
                Span<float> sqr = stackalloc float[_zone.Spawns.Count];

                for (int i = 0; i < _zone.Spawns.Count; i++) // get the furthest spawn point away from the good team as the initial spawn for the evil team
                {
                    float d = (_zone.Spawns[i] - goodSpawn).sqrMagnitude;
                    sqr[i] = d;

                    if (d > maxSqr)
                    {
                        maxSqr = d;
                        evilSpawn = _zone.Spawns[i];
                    }
                }

                float minSqr = maxSqr * 0.5625f; // 75 % gap (0.75)²
                float teamSqr = minSqr * 0.25f; // 25 % of arena‑diameter²
                using var evilSpawns = GetPooledList<Vector3>(); // ≥ 75% away from Good
                using var goodSpawns = GetPooledList<Vector3>(); // ≥ 75% away from Evil

                for (int i = 0; i < _zone.Spawns.Count; i++)
                {
                    Vector3 p = _zone.Spawns[i];
                    bool farFromGoodPrimary = sqr[i] >= minSqr; // distance to goodSpawn
                    bool farFromEvilPrimary = (p - evilSpawn).sqrMagnitude >= minSqr;

                    // Assign to the side that needs it most but keep both constraints where its ≥75 % from the other team, and ≤√teamSqr from mate
                    if (farFromGoodPrimary && CloseToAny(evilSpawns, p, teamSqr) && FarFromAll(goodSpawns, p, minSqr) && (!farFromEvilPrimary || evilSpawns.Count > goodSpawns.Count || !FarFromAll(evilSpawns, p, minSqr)))
                    {
                        evilSpawns.Add(p);
                    }
                    else if (farFromEvilPrimary && CloseToAny(goodSpawns, p, teamSqr) && FarFromAll(evilSpawns, p, minSqr))
                    {
                        goodSpawns.Add(p);
                    }
                }

                env.SubscribeHooks(true);

                EnsureSpawnCapacity(goodSpawns, evilSpawns, minSqr, _zone.MaxY, Good.Players.Count, env.jitteredSpawns); // ensure sufficient spawn points
                EnsureSpawnCapacity(evilSpawns, goodSpawns, minSqr, _zone.MaxY, Evil.Players.Count, env.jitteredSpawns);

                Spawn(evilSpawns, goodSpawns);
            }

            private bool CloseToAny(List<Vector3> pts, Vector3 p, float maxSqr) // ⇒ cohesion within a team
            {
                if (pts.Count == 0)
                    return true;
                for (int k = 0; k < pts.Count; k++)
                    if ((p - pts[k]).sqrMagnitude <= maxSqr) // close enough ⇒ accept
                        return true;
                return false; // too far ⇒ reject
            }

            private bool FarFromAll(List<Vector3> pts, Vector3 p, float minSqr) // ⇒ separation between teams
            {
                for (int k = 0; k < pts.Count; k++)
                    if ((p - pts[k]).sqrMagnitude < minSqr)
                        return false; // too close ⇒ reject
                return true; // far enough ⇒ accept
            }

            private Vector3 Closest(List<Vector3> pts, Vector3 p)
            {
                Vector3 closest = pts[0];
                float best = float.MaxValue;
                for (int i = 0; i < pts.Count; i++)
                {
                    float d = (pts[i] - p).sqrMagnitude;
                    if (d < best)
                    {
                        best = d;
                        closest = pts[i];
                    }
                }
                return closest;
            }

            public const float SELF_EPS_SQR = 0.04f * 0.04f; // 4 cm radius ⇒ “same spot”

            private void EnsureSpawnCapacity(List<Vector3> spawns, List<Vector3> opposing, float minSqr, float maxY, int required, bool jitterFirst)
            {
                if (spawns.Count == 0) 
                    return;

                int root = 0;
                int tries = 0;
                int cap = required * 32;
                int baseCount = spawns.Count; // loop bounds

                while (spawns.Count < required && tries++ < cap)
                {
                    Vector3 seed = spawns[root]; // pick root
                    root = (root + 1) % spawns.Count; // bump & wrap

                    // choose order according to flag
                    if (jitterFirst ? JitterRing(seed) || FanOut(seed) : FanOut(seed) || JitterRing(seed))
                        continue; // placed ⇒ next slot
                }

                while (spawns.Count < required) // absolute fallback with round-robin dup
                    spawns.Add(spawns[spawns.Count % baseCount]); // exact dup

                bool TryAdd(Vector3 pos)
                {
                    if (env.ValidSpawnPoint(pos) && FarFromAll(opposing, pos, minSqr) && FarFromAll(spawns, pos, SELF_EPS_SQR))
                    {
                        spawns.Add(new Vector3(pos.x, pos.y + 0.75f, pos.z)); // add
                        return true;
                    }
                    return false; // reject
                }

                bool JitterRing(Vector3 s) // 25 cm offsets around seed
                {
                    for (int d = 0; d < 8; d++)
                    {
                        Vector3 p = s + env.Dir8[d] * 0.25f; // jitter
                        p.y = GetSpawnHeight(p, maxY);
                        if (TryAdd(p)) return true; // placed
                    }
                    return false; // none fit
                }

                bool FanOut(Vector3 s) // 0.5 m → 4 m radial sweep
                {
                    Vector3 dir = s - Closest(opposing, s); // away
                    if (dir.sqrMagnitude < 0.01f) dir = Vector3.right; // fallback
                    dir.y = 0; dir.Normalize(); // flatten

                    for (float r = 0.5f; r <= 4f; r += 0.5f) // widen, bump r <= 6f if fails too often
                    {
                        Vector3 p = s + dir * r; // straight
                        p.y = GetSpawnHeight(p, maxY);
                        if (TryAdd(p)) return true; // placed

                        for (int d = 0; d < 8; d++) // 8-dir sweep
                        {
                            p = s + env.Dir8[d] * r;
                            p.y = GetSpawnHeight(p, maxY);
                            if (TryAdd(p)) return true; // placed
                        }
                    }
                    return false; // failed
                }
            }

            private void Spawn(PooledList<Vector3> evilSpawns, PooledList<Vector3> goodSpawns)
            {
                Spawn(Good.Players.Values, goodSpawns); // every point ≥75 % from all Evil points
                Spawn(Evil.Players.Values, evilSpawns); // every point ≥75 % from all Good points

                if (RoundIndex == 1)
                {
                    Message(Good.Players.Values, "MatchStarted", GetTeamNames(Team.Evil));
                    Message(Evil.Players.Values, "MatchStarted", GetTeamNames(Team.Good));
                }
                else if (RoundIndex <= TotalRounds)
                {
                    Message(Good.Players.Values, "MatchNextRound", RoundIndex, TotalRounds, GetTeamNames(Team.Evil));
                    Message(Evil.Players.Values, "MatchNextRound", RoundIndex, TotalRounds, GetTeamNames(Team.Good));
                }

                _zone.IsLocked = true;
                IsStarted = true;
            }

            private void Spawn(IEnumerable<BasePlayer> players, List<Vector3> spawns)
            {
                int count = spawns.Count;
                foreach (var player in players)
                {
                    if (count == 0) count = spawns.Count; // recycle if we run out
                    int idx = UnityEngine.Random.Range(0, count--);
                    Vector3 spawn = spawns[idx];
                    (spawns[idx], spawns[count]) = (spawns[count], spawn); // O(1) removal
                    
                    if (player is DuelistNPC)
                        spawn.y -= 0.7f;

                    env.data.Kits[player.UserIDString] = _kit;
                    Vector3 pos = player.transform.position;

                    if (player.IsHuman())
                    {
                        SaveHome(player, pos);
                    }

                    env.RemoveFromQueue(player.UserIDString);
                    env.EnableUserImmunity(player, spawn);
                    env.Teleport(player, spawn, _zone.ProtectionRadius, !_zone.InRange(pos));
                    SetViewingAngles(player, spawn, _zone.Location);
                }
            }

            private void SaveHome(BasePlayer player, Vector3 pos)
            {
                if (!env.DuelTerritory(pos) || !env.data.Homes.ContainsKey(player.UserIDString))
                {
                    if (env.IsOnConstruction(pos)) pos.y += 1; // prevent player from becoming stuck or dying when teleported home
                    env.data.Homes[player.UserIDString] = pos;
                }
            }

            private static void SetViewingAngles(BasePlayer player, Vector3 from, Vector3 to)
            {
                Vector3 dir = to - from;
                if (dir.sqrMagnitude < 0.001f) return; // ignore zero‑length

                Quaternion look = Quaternion.LookRotation(dir, Vector3.up); // full (yaw + pitch)
                Vector3 e = look.eulerAngles;
                Quaternion bodyYaw = Quaternion.Euler(0f, e.y, 0f); // strip pitch/roll

                player.transform.rotation = bodyYaw; // body only yaw
                player.ServerRotation = bodyYaw;
                player.OverrideViewAngles(new Vector3(e.x, e.y, 0f)); // pitch+yaw to client
                player.eyes.NetworkUpdate(bodyYaw); // eyes follow body yaw
                player.SendNetworkUpdateImmediate();
            }
        }

        public class DuelKitItem
        {
            public string ammo;
            public int amount;
            public string container;
            public List<string> mods;
            public string shortname;
            public ulong skin;
            public int slot;
            public DuelKitItem() { }
            public DuelKitItem(string ammo, int amount, string container, List<string> mods, string shortname, ulong skin, int slot)
            {
                this.ammo = ammo;
                this.amount = amount;
                this.container = container;
                this.mods = mods;
                this.shortname = shortname;
                this.skin = skin;
                this.slot = slot;
            }
        }

        public class BetInfo
        {
            [JsonProperty(PropertyName = "amount", NullValueHandling = NullValueHandling.Ignore)]
            public int? amount = null; // amount the player bet
            public string trigger; // the trigger used to request the bet
            public int itemid; // the unique identifier of the item
            public int max; // the maximum amount allowed to bet on this item
            public BetInfo() { }
            public BetInfo(int? amount, string trigger, int max, int itemid)
            {
                this.amount = amount;
                this.trigger = trigger;
                this.max = max;
                this.itemid = itemid;
            }
            public bool Equals(BetInfo bet)
            {
                return bet.amount == amount && bet.itemid == itemid;
            }
        }

        public class DuelingZone : FacepunchBehaviour // Thanks @Jake_Rich for helping me get this started!
        {
            private Dictionary<string, BasePlayer> _players = new();
            private Dictionary<string, BasePlayer> _waiting = new();
            internal HashSet<DuelistNPC> npcs = new();
            internal List<BaseEntity> walls = new();
            private List<Vector3> _spawns;
            private List<Vector3> _duelSpawns = new(); // spawn points generated on the fly
            private List<SphereEntity> spheres = new(); 
            private Vector3 _zonePos, _zonePosXZ3D;
            public float ProtectionRadius, SqrProtectionRadius;
            public string zoneName;
            public bool IsLocked;
            public bool IsFinito;
            public int Kills;
            public GameObject go;
            internal Duelist env;

            public int TotalPlayers => _players.Count;

            public PooledList<BasePlayer> Players => GetPooledList(_players.Values);

            public void ClearSpawns() => _spawns = null;

            public List<Vector3> Spawns
            {
                get
                {
                    if (_spawns == null)
                    {
                        _spawns = env.GetSpawnPoints(this); // get custom spawn points if any exist
                    }
                    return _spawns.Count < 2 ? _duelSpawns : _spawns;
                }
            }

            public bool IsFull => IsLocked || TotalPlayers + _waiting.Count + 2 > env.playersPerZone;

            public float MaxY => Location.y + ProtectionRadius;

            public Vector3 Location => _zonePos;

            public Vector3 LocationXZ3D => _zonePosXZ3D;

            private void Message(BasePlayer player, string key, params object[] args) => env.Message(player, key, args);

            private void OnDestroy()
            {
                Destroy(go);
                Destroy(this);
            }

            private void OnTriggerEnter(Collider col)
            {
                if (col == null || col.ObjectName() == "ZoneManager")
                    return;

                var entity = col.ToBaseEntity();
                if (entity == null || entity.IsDestroyed)
                    return;

                if (entity is BaseMountable m)
                {
                    using var players = GetMountedPlayers(m);

                    RemoveMountable(m, players);
                }
                else if (entity is BasePlayer p)
                {
                    if (env.IsParticipant(p, true))
                    {
                        return;
                    }

                    RemovePlayer(p);
                }
                else if (IsCustomEntity(entity))
                {
                    RemoveMountable(entity, env._emptyPlayers);
                }
            }

            public Vector3 GetEjectLocation(Vector3 a, float distance)
            {
                Vector3 position = ((a.XZ3D() - LocationXZ3D).normalized * (ProtectionRadius + distance)) + Location; // credits ZoneManager
                position.y = GetSpawnHeight(position, MaxY) + 0.75f;
                return position;
            }

            private bool CanBypass(BasePlayer player) => !env.config.Settings.removeAdmins && player.IsAdmin || !env.config.Settings.removeFlying && player.IsFlying;

            public bool RemovePlayer(BasePlayer player)
            {
                if (!player.IsHuman() || CanBypass(player))
                {
                    return false;
                }

                var m = player.GetMounted();
                if (m.IsValid())
                {
                    using var players = GetMountedPlayers(m);
                    return RemoveMountable(m, players);
                }

                var parent = player.GetParentEntity();
                if (parent != null && IsCustomEntity(parent))
                {
                    return RemoveMountable(parent, env._emptyPlayers);
                }

                var position = GetEjectLocation(player.transform.position, 10f);
                if (player.IsFlying && player.transform.position.y > position.y)
                {
                    position.y = player.transform.position.y;
                }

                player.Teleport(position);
                player.SendNetworkUpdateImmediate();

                return true;
            }

            public void DismountAllPlayers(BaseMountable m)
            {
                using var players = GetMountedPlayers(m);

                foreach (var player in players)
                {
                    m.DismountPlayer(player, false);

                    player.EnsureDismounted();
                }
            }

            private PooledList<BasePlayer> GetMountedPlayers(BaseMountable m)
            {
                BaseVehicle vehicle = m.HasParent() ? m.VehicleParent() : m as BaseVehicle;
                PooledList<BasePlayer> players = GetPooledList<BasePlayer>();

                if (vehicle.IsValid())
                {
                    vehicle.GetMountedPlayers(players);
                    players.RemoveAll(x => x == null || !x.IsHuman());
                    return players;
                }

                var player = m.GetMounted();

                if (player.IsValid() && player.IsHuman())
                {
                    players.Add(player);
                }

                return players;
            }

            private static BaseEntity GetParentEntity(BaseEntity m)
            {
                int n = 0;
                while (m != null && m.HasParent() && ++n < 30)
                {
                    if (!(m.GetParentEntity() is BaseEntity parent)) break;
                    m = parent;
                }

                return m;
            }

            private bool IsFlying(BasePlayer player)
            {
                return player != null && player.modelState != null && !player.modelState.onground && TerrainMeta.HeightMap.GetHeight(player.transform.position) < player.transform.position.y - 1f;
            }

            private bool RemoveMountable(BaseEntity m, List<BasePlayer> players)
            {
                m = GetParentEntity(m);
                if (m is ZiplineMountable or TrainCar { OwnerID: 0uL }) return false;
                if (players.Exists(CanBypass)) return false;

                var j = TerrainMeta.HeightMap.GetHeight(m.transform.position) - m.transform.position.y;
                var distance = 10f + m.bounds.size.Max();

                if (j > 5f)
                {
                    distance += j;
                }

                var position = ((m.transform.position.XZ3D() - LocationXZ3D).normalized * (ProtectionRadius + distance)) + Location;

                if (m is BaseHelicopter or Parachute || players.Exists(IsFlying))
                {
                    position.y = Mathf.Max(m.transform.position.y + 5f, GetSpawnHeight(position, MaxY) + 1f);
                }
                else
                {
                    position.y = GetSpawnHeight(position, MaxY) + 1f;
                }

                MoveAndRotate(m, position);

                return true;
            }

            private static void MoveAndRotate(BaseEntity entity, Vector3 position)
            {
                Rigidbody rb = entity is BaseVehicle vehicle ? vehicle.rigidBody : entity.GetComponent<Rigidbody>();
                Quaternion yaw = Quaternion.AngleAxis(180f, Vector3.up);
                Quaternion pitch = Quaternion.AngleAxis(10f, Vector3.left);
                Quaternion rotation = yaw * entity.transform.rotation * pitch;

                if (rb != null && !rb.isKinematic)
                {
                    entity.transform.rotation = rotation;
                    Vector3 v = yaw * new Vector3(rb.velocity.x, 0f, rb.velocity.z);
                    rb.velocity = new Vector3(v.x, rb.velocity.y, v.z);
                    rb.MovePosition(position);
                    rb.MoveRotation(rotation);
                }
                else
                {
                    entity.transform.SetPositionAndRotation(position, rotation);
                }
            }

            public void Setup(Vector3 position)
            {
                transform.position = _zonePos = position;
                _zonePosXZ3D = position.XZ3D();
                _duelSpawns = env.GetAutoSpawns(this);

                if (env.removePlayers)
                {
                    SetupCollider();
                }

                if (env.autoOvens || env.autoFlames || env.autoTurrets)
                {
                    using var entities = GetPooledList<BaseCombatEntity>();
                    Vis.Entities(Location, ProtectionRadius, entities);

                    foreach (var e in entities)
                    {
                        env.SetupPower(e);
                    }
                }

                CreateSpheres();
            }

            private void SetupCollider()
            {
                go.transform.position = Location;
                go.layer = (int)Layer.Reserved1;

                if (!go.TryGetComponent<SphereCollider>(out var collider))
                {
                    collider = go.AddComponent<SphereCollider>();
                }

                if (collider != null)
                {
                    collider.radius = ProtectionRadius;
                    collider.isTrigger = true;
                    collider.center = Vector3.zero;
                }

                if (!go.TryGetComponent<Rigidbody>(out var rigidbody))
                {
                    rigidbody = go.AddComponent<Rigidbody>();
                }

                if (rigidbody != null)
                {
                    rigidbody.isKinematic = true;
                    rigidbody.useGravity = false;
                    rigidbody.detectCollisions = true;
                    rigidbody.collisionDetectionMode = CollisionDetectionMode.Discrete;
                }
            }

            private void RemoveSpheres()
            {
                spheres.ForEach(sphere => sphere.SafelyKill());
            }

            private void CreateSpheres()
            {
                if (env.sphereAmount <= 0)
                {
                    return;
                }

                for (int i = 0; i < env.sphereAmount; i++)
                {
                    var sphere = GameManager.server.CreateEntity("assets/prefabs/visualization/sphere.prefab", Location) as SphereEntity;

                    if (sphere == null)
                        continue;

                    sphere.currentRadius = ProtectionRadius * 2f;
                    sphere.lerpRadius = sphere.currentRadius;
                    sphere.OwnerID = DUELIST_ID;
                    sphere.enableSaving = false;
                    sphere.Spawn();
                    spheres.Add(sphere);
                }
            }

            public SimpleBuildingBlock CreateZoneWall(string prefab, Vector3 pos, Quaternion rot, ulong ownerId, Vector3 center = default)
            {
                var e = GameManager.server.CreateEntity(prefab, pos, rot, false) as SimpleBuildingBlock;
                if (e == null)
                    return null;

                if (center != Vector3.zero)
                {
                    e.transform.LookAt(center.WithY(pos.y), Vector3.up); // have each wall look at the center of the zone
                    e.transform.Rotate(0f, 180f, 0f); // rotate the wall so the soft side faces inward
                }

                e.enableSaving = false;
                e.OwnerID = ownerId;
                e.Spawn();
                e.gameObject.SetActive(true);
                e.decay = null;
                e.upkeepTimer = float.MinValue;
                return e;
            }

            public void RemoveZoneWalls()
            {
                if (env.respawnWalls && env.Manager != null)
                {
                    env.Unsubscribe(nameof(OnEntityKill));
                }
                foreach (var entity in walls)
                {
                    entity.SafelyKill();
                }
                if (env.respawnWalls && env.Manager != null)
                {
                    env.Subscribe(nameof(OnEntityKill));
                }
                walls.Clear();
            }

            public void CreateZoneWalls(Vector3 center, float zoneRadius, string prefab, BasePlayer player = null)
            {
                if (!env.useZoneWalls)
                    return;

                var tick = DateTime.Now;
                var yOverlap = 6f;
                var maxDistance = 48f;
                var maxHeight = -200f;
                var minHeight = 200f;
                var gap = prefab == heswPrefab ? 0.3f : 0.5f; // the distance used so that each wall fits closer to the other so players cannot throw items between the walls
                var next1 = Mathf.CeilToInt(360 / zoneRadius * 0.1375f);
                var next2 = 360 / zoneRadius - gap; // the distance apart each wall will be from the other

                using var vectors1 = env.GetCircumferencePositions(center, zoneRadius, next1, 0f);
                foreach (var position in vectors1) // get our positions and perform the calculations for the highest and lowest points of terrain
                {
                    if (Physics.Raycast(new Vector3(position.x, position.y + 200f, position.z), Vector3.down, out var hit, Mathf.Infinity, wallMask))
                    {
                        maxHeight = Mathf.Max(hit.point.y, maxHeight); // calculate the highest point of terrain
                        minHeight = Mathf.Min(hit.point.y, minHeight); // calculate the lowest point of terrain
                        center.y = minHeight; // adjust the spawn point of our walls to that of the lowest point of terrain
                    }
                }

                int stacks = Mathf.CeilToInt((maxHeight - minHeight) / 6f) + env.extraWallStacks; // get the amount of walls to stack onto each other to go above the highest point
                using var vectors2 = env.GetCircumferencePositions(center, zoneRadius, next2, center.y);
                for (int i = 0; i < stacks; i++) // create our loop to spawn each stack
                {
                    float currentY = center.y + (i * yOverlap);

                    if (currentY - center.y > maxDistance)
                    {
                        break;
                    }

                    foreach (var v in vectors2) // get a list positions where each positions difference is the width of a high external stone wall. specify the height since we've already calculated what's required
                    {
                        Vector3 position = new(v.x, currentY, v.z);
                        float terrainHeight = TerrainMeta.HeightMap.GetHeight(position);

                        if (terrainHeight - currentY > yOverlap) // 0.1.13 improved distance check underground
                            continue;

                        if (env.useLeastAmount && position.y - terrainHeight > 6f + env.extraWallStacks * 6f)
                            continue;

                        if (env.useLeastAmount)
                        {
                            float j = stacks * yOverlap + yOverlap;

                            if (position.y - terrainHeight > j && position.y < terrainHeight)
                            {
                                continue;
                            }
                        }

                        SimpleBuildingBlock e = CreateZoneWall(prefab, position, Quaternion.identity, DUELIST_ID, center);
                        if (e == null)
                            continue;

                        e.debrisPrefab.guid = null;
                        e.canBeDemolished = false;
                        e.Invoke("StopBeingDemolishable", 0f);
                        walls.Add(e); // keep track of walls to delete when zone is destroyed, and serves as our counter too

                        float fractionUnder = Mathf.Clamp01((terrainHeight - currentY) / yOverlap);

                        if (fractionUnder > 0.2f)
                        {
                            FixNav(false, e); // 0.1.16 & 1.3.6: fix for npcs and explosives passing through walls
                        }

                        if (i == stacks - 1 && fractionUnder >= 0.6f)
                        {
                            stacks++;
                            continue;
                        }

                        if (stacks == i - 1 && Physics.Raycast(new Vector3(v.x, v.y + 6.5f, v.z), Vector3.down, out var hit, 13f, worldMask))
                        {
                            if (hit.collider.ObjectName().Contains("rock") || hit.collider.ObjectName().Contains("formation", CompareOptions.OrdinalIgnoreCase))
                            {
                                stacks++; // 0.1.16 fix where rocks could allow a boost in or out of the top of a zone
                            }
                        }
                    }
                }

                if (player == null) Puts(env.msg("GeneratedWalls", null, walls.Count, stacks, env.FormatPosition(center), (DateTime.Now - tick).TotalSeconds));
                else Message(player, "GeneratedWalls", walls.Count, stacks, env.FormatPosition(center), (DateTime.Now - tick).TotalSeconds);
                env.Subscribe(nameof(OnEntityTakeDamage));
            }

            private static void FixNav(bool frontier, SimpleBuildingBlock e)
            {
                MeshCollider mesh = e.GetComponentInChildren<MeshCollider>();
                if (mesh == null || !e.TryGetComponent(out UnityEngine.AI.NavMeshObstacle nav))
                {
                    return;
                }
                if (frontier)
                {
                    nav.size = mesh.bounds.size * 1.1f;
                    nav.center += nav.transform.InverseTransformDirection(new Vector3(0f, 2.25f, -0.5f));
                }
                else
                {
                    nav.size = nav.size.WithY(mesh.bounds.size.y);
                    nav.center = e.transform.InverseTransformPoint(mesh.bounds.center);
                }
            }

            public float Distance(Vector3 position)
            {
                return (Location - position).MagnitudeXZ();
            }

            public float SqrDistance(Vector3 position)
            {
                return (Location - position).SqrMagnitudeXZ();
            }

            public bool InRange(Vector3 position)
            {
                return SqrDistance(position) <= SqrProtectionRadius;
            }

            public SelectionResult GetSelectionResult(BasePlayer player, BasePlayer target, bool isQueued, bool isPaymentRequired, out bool isPaymentCompleted)
            {
                if (IsFull)
                {
                    isPaymentCompleted = false;
                    return SelectionResult.Full;
                }

                var option = env.requiredDuelPaymentOption;
                if (isPaymentRequired && option != null && option.IsEnabled())
                {
                    if (!HasPaymentBalance(option, player))
                    {
                        env.RemoveFromQueue(player.UserIDString);
                        Message(player, "MoneyRequired", option.Amount);

                        if (isQueued)
                        {
                            env.RemoveFromQueue(target.UserIDString);
                            Message(target, "MoneyRequired", option.Amount);
                        }

                        isPaymentCompleted = false;
                        return SelectionResult.PaymentRequired;
                    }

                    if (!HasPaymentBalance(option, target))
                    {
                        env.RemoveFromQueue(target.UserIDString);
                        Message(target, "MoneyRequired", option.Amount);

                        isPaymentCompleted = false;
                        return SelectionResult.PaymentRequired;
                    }

                    TakePaymentBalance(option, player);
                    TakePaymentBalance(option, target);
                }

                _waiting[player.UserIDString] = player;
                _waiting[target.UserIDString] = target;

                isPaymentCompleted = true;
                return SelectionResult.Initiate;
            }

            private bool HasPaymentBalance(CustomCostOption option, BasePlayer player)
            {
                if (option.plugin == null)
                {
                    option.plugin = env.plugins.Find(option.PluginName);
                }

                if (option.plugin != null)
                {
                    double balance = 0;

                    if (!string.IsNullOrWhiteSpace(option.ShoppyStockShopName))
                    {
                        balance = Convert.ToDouble(option.plugin?.Call(option.BalanceHookName, option.ShoppyStockShopName, option.PlayerDataType switch
                        {
                            2 => player,
                            1 => player.UserIDString,
                            0 or _ => (ulong)player.userID
                        }));
                    }
                    else balance = Convert.ToDouble(option.plugin?.Call(option.BalanceHookName, option.PlayerDataType switch
                    {
                        2 => player,
                        1 => player.UserIDString,
                        0 or _ => (ulong)player.userID
                    }));

                    if (balance < option.Amount)
                    {
                        return false;
                    }
                }

                return true;
            }

            private bool TakePaymentBalance(CustomCostOption option, BasePlayer buyer)
            {
                if (option.plugin == null)
                {
                    option.plugin = env.plugins.Find(option.PluginName);
                }

                if (option.plugin != null)
                {
                    if (!string.IsNullOrWhiteSpace(option.ShoppyStockShopName))
                    {
                        option.plugin?.Call(option.WithdrawHookName, option.ShoppyStockShopName, option.PlayerDataType switch
                        {
                            2 => buyer,
                            1 => buyer.UserIDString,
                            0 or _ => (ulong)buyer.userID
                        }, option.AmountDataType switch
                        {
                            2 => (object)(int)option.Amount,
                            1 => (object)(float)option.Amount,
                            0 or _ => (object)(double)option.Amount
                        });

                        return true;
                    }
                    else
                    {
                        option.plugin?.Call(option.WithdrawHookName, option.PlayerDataType switch
                        {
                            2 => buyer,
                            1 => buyer.UserIDString,
                            0 or _ => (ulong)buyer.userID
                        }, option.AmountDataType switch
                        {
                            2 => (object)(int)option.Amount,
                            1 => (object)(float)option.Amount,
                            0 or _ => (object)(double)option.Amount
                        });

                        return true;
                    }
                }

                return false;
            }

            public bool RemoveWait(string playerId)
            {
                return _waiting.Remove(playerId);
            }

            public void AddPlayer(BasePlayer player)
            {
                _players[player.UserIDString] = player;
            }

            public void RemovePlayer(string playerId)
            {
                if (_players.Remove(playerId))
                {
                    RemoveWait(playerId);
                }
            }

            public bool HasPlayer(string playerId)
            {
                return _players.ContainsKey(playerId);
            }

            public void Kill()
            {
                using var players = GetPooledList(_players.Values);
                foreach (var player in players)
                    env.EjectPlayer(player);

                using var targets = GetPlayerList(true);
                foreach (var target in targets)
                {
                    if (Distance(target.transform.position) > ProtectionRadius)
                        continue;

                    env.EndSpectate(target);
                    env.SendHome(target);
                }

                foreach (var npc in npcs)
                {
                    if (npc == null) continue;
                    BasePlayer.bots.Remove(npc);
                    npc.DelayedSafeKill();
                }

                RemoveZoneWalls();
                env.duelingZones.Remove(this);
                _players.Clear();
                RemoveSpheres();
                Destroy(go);
            }
        }

        private class WorldExplosive : FacepunchBehaviour
        {
            public WorldItem worldItem;
            private const float minExplosionRadius = 1f;
            private const float explosionRadius = 5f;
            private const int layers = 141568;

            public void Init(WorldItem wi)
            {
                worldItem = wi;
            }

            private void OnDestroy()
            {
                if (worldItem != null && !worldItem.IsDestroyed)
                {
                    List<DamageTypeEntry> damageTypes = new()
                    {
                        new()
                        {
                            amount = 25f,
                            type = DamageType.Explosion
                        }
                    };

                    if (worldItem.OwnerID == 0uL) worldItem.OwnerID = DUELIST_ID;
                    //Effect.server.Run("some resource", worldItem.PivotPoint(), worldItem.transform.forward, null, true);
                    DamageUtil.RadiusDamage(worldItem, worldItem.LookupPrefab(), worldItem.CenterPoint(), minExplosionRadius, explosionRadius, damageTypes, layers, true);
                }
            }
        }

        public class DuelistNPC : ScientistNPC
        {
            public new DuelistBrain Brain;

            public string DisplayNameOverride;

            public new Translate.Phrase LootPanelTitle => DisplayNameOverride;

            public override string Categorize() => "Duelist";

            public override bool ShouldDropActiveItem() => false;

            public override string displayName => DisplayNameOverride;

            public override bool IsNpc => false;
        }

        public class DuelistBrain : ScientistBrain
        {
            internal string displayName;
            internal string AttackName = string.Empty;
            internal Transform NpcTransform;
            internal IThinker thinker;
            internal DuelistNPC npc;
            internal Duelist Instance;
        }

        private void Init()
        {
            MaxTerrainY = 150f;
            SubscribeHooks(false); // turn off all hooks immediately
        }

        private void OnServerInitialized()
        {
            RegisterCommands();
            SetupDefinitions();

            foreach (var monument in UnityEngine.Object.FindObjectsOfType<MonumentInfo>())
            {
                float radius = Mathf.Max(150f, monument.Bounds.size.Max());
                monuments[monument.transform.position] = radius * radius;
            }

            try { data = Interface.Oxide.DataFileSystem.ReadObject<StoredData>(Name); } catch { }
            if (data == null) data = new();

            foreach (var bet in cfg_duelingBets) // 0.1.5 fix - check itemList after server has initialized
            {
                if (ItemManager.FindItemDefinition(bet.itemid) == null)
                {
                    Puts("Bet itemid {0} is invalid.", bet.itemid);
                }
                else duelingBets.Add(bet);
            }

            if (useAnnouncement && announceTime > 0f)
                announceTimer = timer.Repeat(announceTime, 0, () => DuelAnnouncement(false));

            eventTimer = timer.Every(0.5f, CheckDuelistMortality); // kill players who haven't finished their duel in time. remove temporary immunity for duelers when it expires

            if (!resetDuelists && BuildingManager.server.buildingDictionary.Count == 0)
            {
                if (data.Get(Points.VictorySeed).Count > 0 && data.Get(Points.VictorySeed).Values.Exists(x => x > 0))
                {
                    resetDuelists = true;
                }
            }

            if (resetDuelists) // map wipe detected - award duelers and reset the data for the seed only
            {
                ResetDuelists();
                resetDuelists = false;
            }

            if (BasePlayer.activePlayerList.Count == 0)
            {
                RemoveZeroStats();
                ResetTemporaryData();
            }

            SetupManagedZones();
            SetupDuelZones();

            if (duelingZones.Count > 0 && autoEnable)
                data.DuelsEnabled = true;

            UpdateStability();
            CheckZoneHooks();

            if (guiAutoEnable)
            {
                Subscribe(nameof(OnPlayerConnected));

                using var targets = GetPlayerList();
                foreach (var target in targets)
                    OnPlayerConnected(target);
            }

            _allyCo = ServerMgr.Instance.StartCoroutine(SetupAllyEntitiesCo());
            InitializeDefinitions();

            //if (useInvisibility) InitializeNetworking();
            LoadOwnership();
        }

        private void OnServerSave()
        {
            timer.Once(5f, SaveData);
        }

        private void OnNewSave(string filename)
        {
            resetDuelists = true;
        }

        private object OnDangerousOpen(Vector3 treasurePos)
        {
            return DuelTerritory(treasurePos) ? true : (object)null;
        }

        private object OnPlayerDeathMessage(BasePlayer victim, HitInfo info) // private plugin hook
        {
            return DuelTerritory(victim.transform.position) ? true : (object)null;
        }

        private void Unload()
        {
            foreach (var obj in _trackers.Values)
                if (obj != null) UnityEngine.Object.Destroy(obj);

            if (_allyCo != null)
                ServerMgr.Instance.StopCoroutine(_allyCo);

            DestroyAll();
            eventTimer?.Destroy();
            announceTimer?.Destroy();

            using var matches = GetPooledList(tdmMatches);
            foreach (var match in matches)
            {
                match.IsOver = true;
                match.End();
            }

            using var zones = GetPooledList(duelingZones);
            foreach (var zone in zones)
            {
                RemoveEntities(zone);
                zone.Kill();
            }

            //if (useInvisibility)
            //EntityDestroyOnClient();

            tdmMatches.Clear();
            duelingZones.Clear();
            ResetTemporaryData();
            DestroyAllUI();
            MaxTerrainY = 0f;
        }

        private void OnPlayerDisconnected(BasePlayer player, string reason)
        {
            GetDeathmatch(player, out var match);

            if (match != null && !match.IsStarted && match.EitherEmpty)
                match.End();

            string uid = player.UserIDString;
            if (IsDuelist(uid))
            {
                TryAddDisconnect(uid);
                OnDuelistLost(player, true, false);
                RemoveDuelist(uid);
                ResetDuelist(uid, false);
            }
            else if (match != null && match.IsStarted && !match.IsOver)
            {
                TryAddDisconnect(uid);
                match.RoundsLeft.Remove(uid);
                player.inventory.Strip();
                DefeatMessage(player, match);
                match.CanRematch = false;
                match.RemoveMatchPlayer(player);
            }
            else if (IsSpectating(player))
            {
                TryAddDisconnect(uid);
                EndSpectate(player);
                SendHome(player);
            }

            if (!AnyParticipants())
                Unsubscribe(nameof(OnPlayerDisconnected)); // nothing else to do right now, unsubscribe the hook
        }

        private void OnPlayerConnected(BasePlayer player)
        {
            if (!player.IsValid())
                return;

            if (!player.CanInteract())
            {
                timer.Once(1f, () => OnPlayerConnected(player));
                return;
            }

            createUI.Remove(player.UserIDString);
            cmdDUI(player, szUIChatCommand, Array.Empty<string>());
        }

        private void OnPlayerSleepEnded(BasePlayer player) // setup the player
        {
            if (player == null)
                return;
            string playerId = player.UserIDString;
            if (GetDuelist(player, out var dat))
            {
                if (IsExploiting(player, true))
                {
                    return;
                }

                foreach (var zone in duelingZones)
                {
                    if (zone.RemoveWait(playerId))
                    {
                        if (deathTime > 0)
                        {
                            if (!dataDeath.ContainsKey(playerId))
                            {
                                Message(player, "ExecutionTime", deathTime);
                            }

                            dataDeath[playerId] = Time.time + deathTime * 60;
                        }

                        EndSpectate(player);
                        player.equippingBlocked = true;
                        GivePlayerKit(player, false);
                        player.equippingBlocked = false; 
                        SetEscapedEventTracker(player, true, true);
                        Metabolize(player, true);

                        if (DestroyUI(player) && !createUI.Contains(playerId))
                            createUI.Add(playerId);

                        CheckAutoReady(player);
                        zone.AddPlayer(player);

                        if (useInvisibility)
                            Disappear(player);

                        Interface.Oxide.CallHook("EnableBypass", (ulong)player.userID);
                        HolsterWeapon(player);
                    }
                }

                return;
            }
            else if (GetDeathmatch(player, out var match))
            {
                if (IsExploiting(player, false))
                {
                    return;
                }

                if (deathTime > 0)
                {
                    if (match.RoundIndex <= 1) Message(player, "ExecutionTime", deathTime);
                    dataDeath[playerId] = Time.time + deathTime * 60;
                }

                if (DestroyUI(player) && !createUI.Contains(playerId))
                {
                    createUI.Add(playerId);
                }

                EndSpectate(player);
                player.equippingBlocked = true;
                GivePlayerKit(player, true);
                player.equippingBlocked = false;
                match.GiveShirt(player);
                SetEscapedEventTracker(player, true, false);
                Metabolize(player, true);
                CheckAutoReady(player);

                if (useInvisibility)
                    Disappear(player);

                Interface.Oxide.CallHook("EnableBypass", (ulong)player.userID);
                HolsterWeapon(player);
                return;
            }
            else SetPlayerTime(player, false);

            if (announcements.Remove(playerId, out var announcement))
            {
                CreateAnnouncementUI(player, announcement);
            }

            if (!AnyParticipants() && announcements.Count == 0)
            {
                // nothing else to do right now, unsubscribe the hook
                Unsubscribe(nameof(OnPlayerSleepEnded));
            }
        }

        private void OnPlayerRespawned(BasePlayer player)
        {
            if (DuelTerritory(player.transform.position) && !IsParticipant(player, true))
            {
                var spawnPoint = ServerMgr.FindSpawnPoint();
                int retries = 25;

                while (DuelTerritory(spawnPoint.pos) && --retries > 0)
                    spawnPoint = ServerMgr.FindSpawnPoint();

                Teleport(player, spawnPoint.pos);
            }
        }

        private void OnEntityKill(SimpleBuildingBlock e)
        {
            if (!e.IsKilled() && e.ShortPrefabName.Contains("wall.external.high"))
            {
                var zone = GetDuelZone(e.transform.position, 5f);

                if (zone != null)
                {
                    zone.CreateZoneWall(e.PrefabName, e.transform.position, e.transform.rotation, e.OwnerID);
                }
            }
        }

        private void OnEntityDeath(SimpleBuildingBlock entity, HitInfo info)
        {
            if (entity == null || entity.IsDestroyed)
                return;

            if (respawnWalls && entity.OwnerID == DUELIST_ID && entity.ShortPrefabName.Contains("wall.external.high"))
            {
                var zone = GetDuelZone(entity.transform.position, 5f);
                if (zone != null)
                {
                    zone.CreateZoneWall(entity.PrefabName, entity.transform.position, entity.transform.rotation, entity.OwnerID);
                }
                return;
            }
        }
        
        private void OnEntityDeath(BasePlayer victim, HitInfo info) // 0.1.16 fix for player suiciding
        {
            if (victim == null || victim.IsDestroyed)
                return;

            if (IsSpectator(victim))
                EndSpectate(victim);

            if (IsDueling(victim))
            {
                victim.inventory.Strip();
                OnDuelistLost(victim, true, true);
            }
            else if (GetDeathmatch(victim, out var match))
            {
                victim.inventory.Strip();
                DefeatMessage(victim, match);
                match.RemoveMatchPlayer(victim);
            }
        }

        private void OnPlayerHealthChange(BasePlayer player, float oldValue, float newValue)
        {
            if (newValue < 6f && (player.IsHuman() || player is DuelistNPC))
            {
                if (IsDueling(player))
                {
                    player.health = 6f;
                    player.inventory.Strip();
                    OnDuelistLost(player, false, true);
                }
                else if (GetDeathmatch(player, out var match))
                {
                    player.health = 6f;
                    player.inventory.Strip();
                    DefeatMessage(player, match);
                    match.RemoveMatchPlayer(player);
                }
            }
        }

        private object OnEntityTakeDamage(BaseCombatEntity entity, HitInfo info)
        {
            if (entity.IsKilled() || entity is BaseNpc or BaseNPC2)
                return null;

            if (entity.OwnerID == DUELIST_ID)
            {
                SafelyHeal(entity);
                CancelDamage(info);
                return true;
            }

            if (info == null || info.Initiator.IsKilled() || !info.hasDamage)
                return null;

            BasePlayer victim = entity as BasePlayer;
            BasePlayer attacker = info.Initiator as BasePlayer;
            bool isVic = !victim.IsKilled();
            bool isAtk = !attacker.IsKilled();
            bool vdt = DuelTerritory(entity.transform.position);
            bool adt = DuelTerritory(info.Initiator.transform.position);
            bool avdt = vdt || adt;

            if (adt && entity is PatrolHelicopter)
                return true;

            if (vdt && isVic && info.Initiator is SimpleBuildingBlock) // 1.0.2 - exploit fix
                return true;

            if (isVic && isAtk && victim == attacker) // allow player to suicide and self inflict
            {
                if (info.damageTypes.Has(DamageType.Suicide) && IsParticipant(victim))
                {
                    TryAddSuicide(victim.UserIDString);
                }

                return null;
            }

            if (isVic && info.damageTypes.GetMajorityDamageType() == DamageType.Fall && !UserHasImmunity(victim.UserIDString))
                return null;

            if (isAtk && spectators.Contains(attacker.UserIDString)) // 0.1.27: someone will find a way to abuse spectate mode so we'll prevent that now
            {
                if (!adt)
                {
                    EndSpectate(attacker);
                    SendHome(attacker);
                }

                CancelDamage(info);
                return true;
            }

            if (avdt) // 1.2.0
            {
                if (info.Initiator is BaseNpc animal)
                {
                    if (animal != null)
                    {
                        if (putToSleep)
                        {
                            animal.SetAiFlag(BaseNpc.AiFlags.Sleeping, true);
                            animal.CurrentBehaviour = BaseNpc.Behaviour.Sleep;
                        }
                        else if (killNpc)
                        {
                            animal.Kill();
                        }

                        return true;
                    }
                }
                else if (info.Initiator is BaseNPC2 npc2)
                {
                    if (killNpc) npc2.Kill();
                    return true;
                }
                else if (info.Initiator is BasePlayer npc && !npc.userID.IsSteamId())
                {
                    if (npc is global::HumanNPC human)
                    {
                        human.LootSpawnSlots = Array.Empty<LootContainer.LootSpawnSlot>();
                    }

                    npc.Kill();
                    CancelDamage(info);
                    return true;
                }
            }

            if (_duelists.Count > 0)
            {
                if (isAtk && isVic && GetDuelist(attacker, out var attackerData) && attackerData.ID != victim.UserIDString) // 0.1.8 check attacker then victim
                    return true; // prevent attacker from doing damage to others

                if (isVic && GetDuelist(victim, out var victimData)) // 1.2.0 NRE get_transform
                {
                    if (victim.health == 6f)
                        return true; // don't let the player die, match will complete without the annoyance of death
                    if (UserHasImmunity(victim.UserIDString))
                        return true; // immunity timer
                    if (info.Initiator is PatrolHelicopter)
                        return true; // protect duelers from helicopters
                    if (isAtk && victimData.ID != attacker.UserIDString)
                        return true; // prevent either attacker from doing damage to others
                    info.damageTypes.ScaleAll(damageScaleAmount);
                    return null;
                }
            }

            if (tdmMatches.Count > 0)
            {
                if (isVic && isAtk && GetDeathmatch(attacker, out var match))
                {
                    if (match.GetTeam(victim) == Team.None)
                        return true;

                    if (!dmFF && match.GetTeam(victim) == match.GetTeam(attacker))
                        return true; // FF
                }

                if (isVic && InDeathmatch(victim))
                {
                    if (UserHasImmunity(victim.UserIDString))
                        return true;

                    if (info.Initiator is PatrolHelicopter)
                        return true;

                    if (isAtk)
                    {
                        if (!InDeathmatch(attacker))
                            return true;

                        if (victim.health == 6f)
                            return true;

                        if (!tdmAttackers.TryGetValue(victim.UserIDString, out var p))
                            tdmAttackers[victim.UserIDString] = p = new();

                        p.AttackerName = attacker.displayName;
                        p.AttackerId = attacker.UserIDString;
                        p.Distance = $"{(attacker.transform.position - victim.transform.position).magnitude:N2}";
                        p.BoneName = info.boneName ?? info.boneArea.ToString();
                        p.def = attacker.GetActiveItem()?.info;
                        p.Weapon = p?.def?.displayName?.english ?? info?.WeaponPrefab?.ShortPrefabName ?? "??";

                        if (p.Weapon.EndsWith(".entity"))
                        {
                            p.def = ItemManager.FindItemDefinition(p.Weapon.Replace(".entity", string.Empty).Replace("_", "."));
                            p.Weapon = p.def?.displayName.translated ?? p.Weapon.Replace(".entity", string.Empty).Replace("_", string.Empty).SentenceCase();
                        }
                    }

                    info.damageTypes.ScaleAll(damageScaleAmount);
                    return null;
                }
            }

            if (isVic && isAtk) // 1.1.1 - fix for players standing on the edge of a zone for protection
            {
                if (vdt && !IsParticipant(victim.UserIDString))
                    return null;

                if (adt && !IsParticipant(attacker.UserIDString))
                    return null;
            }

            if (adt && !vdt)
                return true; // block all damage to the outside

            if (!adt && vdt)
                return true; // block all damage to the inside

            return null;
        }

        private object CanRevivePlayer(BasePlayer player, Vector3 pos)
        {
            return InEvent(player) ? true : (object)null;
        }

        private object OnLifeSupportSavingLife(BasePlayer player)
        {
            return InEvent(player) ? true : (object)null;
        }

        private object OnRestoreUponDeath(BasePlayer player)
        {
            return InEvent(player) ? true : (object)null;
        }

        private void OnEntitySpawned(WorldItem worldItem)
        {
            if (worldItem.IsKilled() || !DuelTerritory(worldItem.transform.position))
                return;
            NextTick(() =>
            {
                if (!worldItem.IsKilled() && worldItem.item != null && worldItem.item.info.shortname == "arrow.bone")
                {
                    worldItem.gameObject.AddComponent<WorldExplosive>().Init(worldItem);
                }
            });
            if (data.Homes.Count > 0)
            {
                NextTick(() => // prevent rpc kick by using NextTick since we're also hooking OnItemDropped
                {
                    if (!worldItem.IsKilled()) // we must check this or you will still be rpc kicked
                    {
                        if (worldItem != null && worldItem.item != null && !IsThrownWeapon(worldItem.item)) // allow thrown weapons / destroy items which are dropped by players and on death
                            worldItem.Kill();
                    }
                });

                if (!worldItem.IsKilled())
                {
                    timer.Repeat(0.1f, 20, () => // track the item to make sure it wasn't thrown out of the dueling zone
                    {
                        if (!worldItem.IsKilled() && !DuelTerritory(worldItem.transform.position))
                            worldItem.Kill(); // destroy items which are dropped from inside to outside of the zone
                    });
                }
            }

            //void SafelyRemoveBackpack(DroppedItemContainer c)
            //{
            //    List<string> duelers = new List<string>();
            //    GetAllDuelers(duelers);
            //    ServerMgr.Instance.Invoke(() =>
            //    {
            //        if (c != null && duelers.Contains(c.playerSteamID.ToString()))
            //        {
            //            c.SafelyKill();
            //        }
            //    }, 0.1f);
            //}
        }

        private void OnEntitySpawned(BaseEntity entity)
        {
            if (entity == null || entity.IsDestroyed)
                return;

            var position = entity.transform.position;
            var zone = GetDuelZone(position, 5f);
            if (zone == null)
                return;

            if (entity.IsNpc)
            {
                NextTick(entity.SafelyKill);
                return;
            }

            if (autoOvens && entity is BaseOven || autoTurrets && entity is AutoTurret || autoFlames && entity is FlameTurret)
            {
                SetupPower(entity);
                return;
            }

            if (noStability && entity is BuildingBlock block)
            {
                if (block.OwnerID == 0 || permission.UserHasGroup(block.OwnerID.ToString(), "admin"))
                {
                    block.grounded = true;
                    return;
                }
            }

            if (!AnyParticipants())
            {
                return;
            }

            if (prefabs.ContainsKey(entity.PrefabName))
            {
                if (entity.PrefabName.Contains("barricade."))
                {
                    if (morphBarricadesStoneWalls || morphBarricadesWoodenWalls)
                    {
                        var wall = zone.CreateZoneWall(morphBarricadesStoneWalls ? heswPrefab : hewwPrefab, position, entity.transform.rotation, entity.OwnerID);

                        if (wall != null)
                        {
                            entity.SafelyKill();

                            if (!duelEntities.TryGetValue(wall.OwnerID, out var entities))
                                duelEntities.Add(wall.OwnerID, entities = new());

                            entities.Add(wall);
                            return;
                        }
                    }
                }

                if (!duelEntities.TryGetValue(entity.OwnerID, out var entities2))
                    duelEntities.Add(entity.OwnerID, entities2 = new());

                entities2.Add(entity);
            }
            //if (entity is PlayerCorpse corpse && HasEvent(corpse.playerSteamID.ToString())) 
            //{
            //    NextTick(entity.SafelyKill);
            //}
            //else if (entity.ShortPrefabName.Equals("item_drop_backpack") && entity is DroppedItemContainer c)
            //{
            //    SafelyRemoveBackpack(c);
            //}
        }

        private object CanBuild(Planner planner, Construction prefab, Construction.Target target)
        {
            var player = planner.GetOwnerPlayer();
            if (player == null || player.IsAdmin)
                return null;

            var buildPos = target.entity && target.entity.transform && target.socket ? target.GetWorldPosition() : target.position;
            if (DuelTerritory(buildPos, buildingBlockExtensionRadius)) // extend the distance by the configured amount
            {
                if (config.Deployables.Allowed.Count > 0 && prefabs.TryGetValue(prefab.fullName, out var displayName) && config.Deployables.Allowed.TryGetValue(displayName, out var enabled) && enabled && IsParticipant(player.UserIDString))
                {
                    return null;
                }

                Message(player, "Building is blocked!");
                return false;
            }

            return null;
        }

        private object CanLootEntity(BasePlayer player, BaseEntity entity) // stop all players from looting anything inside of dueling zones. this allows server owners to setup duels anywhere without worry.
        {
            if (player == null || player.IsAdmin)
                return null;

            if (InEvent(player, true))
                return true;

            if (!AnyParticipants(true))
                Unsubscribe(nameof(CanLootEntity));

            return null;
        }

        private object CanCreateWorldProjectile(HitInfo info, ItemDefinition itemDef) // prevents thrown items from becoming stuck in players when they respawn and requiring them to relog to remove them
        {
            if (info == null)
                return null;

            if (!AnyParticipants(true))
            {
                Unsubscribe(nameof(CanCreateWorldProjectile));
                return null;
            }

            //if (itemDef.shortname.Contains("arrow") && DuelTerritory(info.HitPositionWorld))
            //    return true;

            if (DuelTerritory(info.HitPositionWorld))
                return true;

            //var victim = info.HitEntity as BasePlayer;
            //if (InEvent(victim))
            //    return true; // non-bool hook, block it

            //var attacker = info.Initiator as BasePlayer;
            //if (InEvent(attacker))
            //    return true;

            return null;
        }

        private void OnItemDropped(Item item, BaseEntity entity)
        {
            if (!AnyParticipants(true)) // nothing left to do here, unsubscribe the hook
            {
                Unsubscribe(nameof(OnItemDropped));
                return;
            }

            var player = item.GetOwnerPlayer();
            if (player == null)
                return;

            if (!IsThrownWeapon(item) && (InEvent(player) || DuelTerritory(entity.transform.position)))
                item.Remove(0.01f); // do NOT allow players to drop items
        }

        private object IsPrisoner(BasePlayer player) // Random Warps
        {
            return DuelTerritory(player.transform.position) ? (object)true : null;
        }

        private object CanEventJoin(BasePlayer player) // EventManager
        {
            return DuelTerritory(player.transform.position) ? msg("CannotEventJoin", player.UserIDString) : null;
        }

        private object canRemove(BasePlayer player) // RemoverTool
        {
            return DuelTerritory(player.transform.position) ? (object)false : null;
        }

        private object CanTrade(BasePlayer player) // Trade
        {
            return DuelTerritory(player.transform.position) ? (object)false : null;
        }

        private object CanBank(BasePlayer player)
        {
            return DuelTerritory(player.transform.position) ? msg("CannotBank", player.UserIDString) : null;
        }

        private object CanOpenBackpack(BasePlayer player)
        {
            return DuelTerritory(player.transform.position) ? msg("CommandNotAllowed", player.UserIDString) : null;
        }

        private object canShop(BasePlayer player) // Shop and ServerRewards
        {
            return DuelTerritory(player.transform.position) ? msg("CannotShop", player.UserIDString) : null;
        }

        private object CanShop(BasePlayer player)
        {
            return DuelTerritory(player.transform.position) ? msg("CannotShop", player.UserIDString) : null;
        }

        private object CanBePenalized(BasePlayer player) // ZLevels Remastered
        {
            return DuelTerritory(player.transform.position) || IsDuelist(player.UserIDString) ? (object)false : null;
        }

        private object canTeleport(BasePlayer player) // 0.1.2: block teleport from NTeleportation plugin
        {
            return DuelTerritory(player.transform.position) ? msg("CannotTeleport", player.UserIDString) : null;
        }

        private object CanTeleport(BasePlayer player) // 0.1.2: block teleport from MagicTeleportation plugin
        {
            return DuelTerritory(player.transform.position) ? msg("CannotTeleport", player.UserIDString) : null;
        }

        private object CanJoinTDMEvent(BasePlayer player)
        {
            return DuelTerritory(player.transform.position) ? (object)false : null;
        }

        private object CanEntityTakeDamage(BasePlayer player, HitInfo info) // TruePVE!!!! <3 @ignignokt84
        {
            return IsParticipant(player) && DuelTerritory(player.transform.position) && (info == null || DuelTerritory(info.PointStart)) ? (object)true : null;
        }

        private object CanJoinAimTrain(BasePlayer player)
        {
            if (InQueue(player.UserIDString) || IsParticipant(player) || DuelTerritory(player.transform.position))
            {
                return false;
            }

            return null;
        }

        private object OnPlayerCommand(BasePlayer player, string command, string[] args)
        {
            if (!player.IsValid() || player.IsDestroyed || InQueue(player.UserIDString))
            {
                return null;
            }

            if (DuelTerritory(player.transform.position))
            {
                command = command.ToLower();
                if (useBlacklistCommands && blacklistCommands.Exists(entry => entry.Replace("/", string.Empty).Equals(command, StringComparison.OrdinalIgnoreCase)))
                {
                    Message(player, "CommandNotAllowed");
                    return true;
                }

                if (useWhitelistCommands && !whitelistCommands.Exists(entry => entry.Replace("/", string.Empty).Equals(command, StringComparison.OrdinalIgnoreCase)))
                {
                    Message(player, "CommandNotAllowed");
                    return true;
                }
            }

            return null;
        }

        private object OnServerCommand(ConsoleSystem.Arg arg)
        {
            var player = arg.Player();

            if (!player.IsValid() || player.IsDestroyed || InQueue(player.UserIDString))
            {
                return null;
            }

            if (DuelTerritory(player.transform.position))
            {
                string command = arg.cmd.FullName.ToLower();

                if (useBlacklistCommands && blacklistCommands.Exists(entry => entry.Replace("/", string.Empty).Equals(command, StringComparison.OrdinalIgnoreCase)))
                {
                    Message(player, "CommandNotAllowed");
                    return true;
                }

                if (useWhitelistCommands && !whitelistCommands.Exists(entry => entry.Replace("/", string.Empty).Equals(command, StringComparison.OrdinalIgnoreCase)))
                {
                    Message(player, "CommandNotAllowed");
                    return true;
                }
            }

            return null;
        }

        private void CommandDeathmatch(IPlayer user, string command, string[] args)
        {
            BasePlayer player = user.Object as BasePlayer;
            if (player == null)
                return;

            if (player.IsAdmin && args.Contains("showall"))
            {
                foreach (var match in tdmMatches)
                {
                    Message(player, "InMatchListGood", match.GetTeamNames(Team.Good));
                    Message(player, "InMatchListEvil", match.GetTeamNames(Team.Evil));
                }

                return;
            }

            if (player.IsAdmin && args.Contains("npc_test"))
            {
                if (!IsNewman(player)) { Message(player, "MustBeNaked"); return; }
                player.inventory.Strip();
                FillDeathmatchNpcQueue(player);
                return;
            }

            if (args.Contains("remove"))
            {
                CommandDuelist(user, command, args);
                return;
            }

            if (!DuelsEnabled(player.UserIDString))
            {
                Message(player, "MustAllowDuels", szDuelChatCommand);
                return;
            }

            if (IsDueling(player))
            {
                Message(player, "AlreadyInADuel");
                return;
            }

            GetDeathmatch(player, out var deathmatch);

            if (deathmatch != null && deathmatch.IsStarted)
            {
                Message(player, "MatchStartedAlready");
                return;
            }

            if (args.Length == 0)
            {
                if (deathmatch == null)
                {
                    if (!autoAllowAll)
                        Message(player, "HelpAllow", szDuelChatCommand);

                    Message(player, "MatchChallenge0", szMatchChatCommand);
                    Message(player, "MatchChallenge2", szMatchChatCommand);
                    Message(player, "MatchChallenge3", szMatchChatCommand);
                    Message(player, "MatchAccept", szMatchChatCommand);
                    Message(player, "MatchCancel", szMatchChatCommand);
                    Message(player, "MatchLeave", szMatchChatCommand);
                    Message(player, "MatchSize", szMatchChatCommand, minDeathmatchSize);
                    Message(player, "MatchKickBan", szMatchChatCommand);
                    Message(player, "MatchSetCode", szMatchChatCommand);
                    Message(player, "MatchTogglePublic", szMatchChatCommand);
                    Message(player, "MatchKit", szMatchChatCommand);
                    Message(player, "UI_Help", szUIChatCommand);
                }
                else
                {
                    Message(player, msg("MatchLeave", player.UserIDString, szMatchChatCommand));

                    if (!deathmatch.IsHost(player))
                        return;

                    Message(player, "MatchCancel", szMatchChatCommand);
                    Message(player, "MatchSize", szMatchChatCommand, minDeathmatchSize);
                    Message(player, "MatchKickBan", szMatchChatCommand);
                    Message(player, "MatchSetCode", szMatchChatCommand);
                    Message(player, "MatchTogglePublic", szMatchChatCommand);
                    Message(player, "MatchKit", szMatchChatCommand);
                    Message(player, "InMatchListGood", deathmatch.GetTeamNames(Team.Good));
                    Message(player, "InMatchListEvil", deathmatch.GetTeamNames(Team.Evil));
                }

                return;
            }

            RemoveRequests(player);

            switch (args[0].ToLower())
            {
                case "autoready":
                    {
                        ToggleAutoReady(player);
                        return;
                    }
                case "rematch":
                case "ready":
                    {
                        ReadyUp(player);
                        return;
                    }
                case "kit": // TDM
                    {
                        if (deathmatch != null)
                        {
                            if (!deathmatch.IsHost(player))
                            {
                                Message(player, "MatchKitSet", deathmatch.Kit);
                                return;
                            }

                            if (args.Length == 2)
                            {
                                string kit = GetVerifiedKit(args[1]);

                                if (string.IsNullOrEmpty(kit))
                                {
                                    Message(player, "MatchChallenge0", szMatchChatCommand);
                                    Message(player, "KitDoesntExist", args[1]);

                                    string kits = string.Join(", ", VerifiedKits);
                                    if (!string.IsNullOrEmpty(kits))
                                        MessageB(player, "Kits: " + kits);
                                }
                                else deathmatch.Kit = kit;
                            }
                            else Message(player, "MatchKit");
                        }
                        else Message(player, "MatchDoesntExist", szMatchChatCommand);

                        return;
                    }
                case "kickban":
                    {
                        if (deathmatch != null)
                        {
                            if (!deathmatch.IsHost(player))
                            {
                                Message(player, "MatchNotAHost");
                                return;
                            }

                            if (args.Length == 2)
                            {
                                var target = BasePlayer.Find(args[1]);

                                if (target != null)
                                {
                                    if (deathmatch.GetTeam(target) == deathmatch.GetTeam(player))
                                    {
                                        if (deathmatch.Ban(target))
                                            Message(player, "MatchBannedUser", target.displayName);
                                        else Message(player, "MatchCannotBan");
                                    }
                                    else Message(player, "MatchPlayerNotFound", target.displayName);
                                }
                                else Message(player, "PlayerNotFound", args[1]);
                            }
                            else Message(player, "MatchKickBan");
                        }
                        else Message(player, "MatchDoesntExist", szMatchChatCommand);

                        break;
                    }
                case "setcode":
                    {
                        if (deathmatch != null)
                        {
                            if (deathmatch.IsHost(player, out var host))
                            {
                                if (args.Length == 2)
                                    deathmatch.SetCode(host, args[1]);

                                Message(player, "MatchCodeIs", host.Code);
                            }
                            else Message(player, "MatchNotAHost");
                        }
                        else Message(player, "MatchDoesntExist", szMatchChatCommand);

                        break;
                    }
                case "cancel":
                case "decline":
                    {
                        if (deathmatch != null)
                        {
                            if (deathmatch.IsHost(player))
                            {
                                deathmatch.MessageAll("MatchCancelled", player.displayName);
                                deathmatch.End();

                                if (tdmMatches.Remove(deathmatch))
                                {
                                    matchUpdateRequired = true;
                                }
                            }
                            else Message(player, "MatchNotAHost");
                        }
                        else // also handle cancelling a match request
                        {
                            if (GetMatchRequestSender(player, out var requesterId) && tdmRequests.Remove(requesterId))
                            {
                                var requester = BasePlayer.Find(requesterId);
                                if (requester != null)
                                    Message(requester, "MatchCancelled", player.displayName);

                                Message(player, "MatchCancelled", player.displayName);
                                return;
                            }

                            if (GetMatchRequestTarget(player, out var targetId) && tdmRequests.Remove(player.UserIDString))
                            {
                                var target = BasePlayer.Find(targetId);
                                if (target != null)
                                    Message(target, "MatchCancelled", player.displayName);

                                Message(player, "MatchCancelled", player.displayName);
                                return;
                            }

                            Message(player, "MatchDoesntExist", szMatchChatCommand);
                        }

                        break;
                    }
                case "size":
                    {
                        if (deathmatch != null)
                        {
                            if (args.Length == 2)
                            {
                                if (int.TryParse(args[1], out int size))
                                {
                                    if (deathmatch.IsHost(player))
                                    {
                                        if (size < minDeathmatchSize)
                                            size = deathmatch.TeamSize;

                                        if (size > maxDeathmatchSize)
                                            size = maxDeathmatchSize;

                                        if (deathmatch.TeamSize != size)
                                            deathmatch.TeamSize = size; // sends message to all players in the match
                                    }
                                    else Message(player, "MatchNotAHost");
                                }
                                else Message(player, "InvalidNumber", args[1]);
                            }
                            else Message(player, "MatchSizeSyntax", szMatchChatCommand);
                        }
                        else Message(player, "MatchDoesntExist", szMatchChatCommand);

                        break;
                    }
                case "accept":
                    {
                        if (IsParticipant(player))
                        {
                            Message(player, "AlreadyDueling");
                            return;
                        }

                        if (!GetMatchRequestSender(player, out var requesterId))
                        {
                            Message(player, "MatchNoneRequested");
                            return;
                        }

                        tdmRequests.Remove(requesterId);

                        var target = BasePlayer.Find(requesterId);

                        if (IsNotConnected(target))
                        {
                            Message(player, "MatchPlayerOffline");
                            break;
                        }

                        SetupTeams(player, target);
                        break;
                    }
                case "leave":
                    {
                        LeaveEvent(player);

                        break;
                    }
                case "any":
                    {
                        if (tdmMatches.Count == 0)
                        {
                            Message(player, "MatchNoMatchesExist", szMatchChatCommand);
                            return;
                        }

                        if (deathmatch != null)
                        {
                            deathmatch.RemoveMatchPlayer(player);
                            Message(player, "MatchPlayerLeft");
                        }

                        foreach (var match in tdmMatches)
                        {
                            if (match.IsBanned(player.userID) || match.IsFull())
                                continue;

                            if (!match.IsFull(Team.Good) && match.IsAlliedTo(player, Team.Good))
                            {
                                match.AddMatchPlayer(player, Team.Good);
                                return;
                            }

                            if (!match.IsFull(Team.Evil) && match.IsAlliedTo(player, Team.Evil))
                            {
                                match.AddMatchPlayer(player, Team.Evil);
                                return;
                            }

                            if (match.IsPublic)
                            {
                                if (!match.IsFull(Team.Good))
                                {
                                    match.AddMatchPlayer(player, Team.Good);
                                    return;
                                }

                                if (!match.IsFull(Team.Evil))
                                {
                                    match.AddMatchPlayer(player, Team.Evil);
                                    return;
                                }
                            }
                        }

                        Message(player, "MatchNoTeamFoundAny", args[0]);
                        break;
                    }
                case "public":
                    {
                        if (deathmatch != null)
                        {
                            if (!deathmatch.IsHost(player))
                            {
                                Message(player, "MatchNotAHost");
                                return;
                            }

                            deathmatch.IsPublic = !deathmatch.IsPublic;
                        }
                        else Message(player, "MatchDoesntExist", szMatchChatCommand);

                        break;
                    }
                default:
                    {
                        if (args.Length > 1)
                        {
                            SetPlayerZone(player, args);

                            foreach (string arg in args)
                            {
                                string kit = GetVerifiedKit(arg); // TDM

                                if (!string.IsNullOrEmpty(kit))
                                {
                                    tdmKits[player.UserIDString] = kit;
                                    break;
                                }
                            }
                        }

                        var target = BasePlayer.Find(args[0]);

                        if (target != null)
                        {
                            if (target == player)
                            {
                                Message(player, "PlayerNotFound", args[0]);
                                return;
                            }

                            if (deathmatch != null)
                            {
                                Message(player, "MatchCannotChallengeAgain");
                                return;
                            }

                            if (IsTeamMember(target) || HasRequestSender(target))
                            {
                                Message(player, "MatchCannotChallenge", target.displayName);
                                return;
                            }

                            if (!IsNewman(player))
                            {
                                Message(player, "MustBeNaked");
                                return;
                            }

                            if (!IsNewman(target))
                            {
                                Message(player, "TargetMustBeNaked");
                                return;
                            }

                            Message(player, "MatchRequestSent", target.displayName);
                            Message(target, "MatchRequested", player.displayName, szMatchChatCommand);

                            string uid = player.UserIDString;
                            tdmRequests[uid] = target.UserIDString;
                            timer.Once(60f, () => tdmRequests.Remove(uid));
                            return;
                        }

                        if (tdmMatches.Count == 0)
                        {
                            Message(player, "MatchNoMatchesExist", szMatchChatCommand);
                            return;
                        }

                        if (deathmatch != null)
                        {
                            deathmatch.RemoveMatchPlayer(player);
                            Message(player, "MatchPlayerLeft");
                        }

                        foreach (var match in tdmMatches)
                        {
                            if (match.IsBanned(player.userID))
                                continue;

                            if (match.GetCode(Team.Good).Equals(args[0], StringComparison.OrdinalIgnoreCase))
                            {
                                match.AddMatchPlayer(player, Team.Good);
                                return;
                            }
                            else if (match.GetCode(Team.Evil).Equals(args[0], StringComparison.OrdinalIgnoreCase))
                            {
                                match.AddMatchPlayer(player, Team.Evil);
                                return;
                            }
                        }

                        Message(player, "MatchNoTeamFoundCode", args[0]);

                    }
                    break;
            }
        }

        private void CommandQueue(IPlayer user, string command, string[] args)
        {
            BasePlayer player = user.Object as BasePlayer;
            if (IsNotConnected(player) || AimTrain.CanCall() && Convert.ToBoolean(AimTrain?.Call("IsAimTraining", (ulong)player.userID)))
            {
                return;
            }

            if (args.Contains("list"))
            {
                Message(player, "InQueueList");
                MessageB(player, string.Join(", ", Queued.Select(kvp => kvp.Value.Name)));
                return;
            }

            if (!player.CanInteract())
            {
                //Message(player, "HelpQueueInteract");
                //timer.Once(1f, () => CommandQueue(user, command, args));
                return;
            }

            if (!DuelsEnabled(player.UserIDString))
            {
                Message(player, "MustAllowDuels", szDuelChatCommand);
                return;
            }

            if (IsTeamMember(player))
            {
                Message(player, "MatchTeamed");
                return;
            }

            if (IsDueling(player))
            {
                Message(player, "AlreadyInADuel");
                return;
            }

            RemoveRequests(player);

            if (!IsNewman(player))
            {
                Message(player, "MustBeNaked");
                return;
            }

            if (!InQueue(player.UserIDString))
            {
                Queued.Add(DateTime.Now.Ticks, new(player));
                Message(player, "InQueueSuccess");
                CheckQueue();
                return;
            }

            if (RemoveFromQueue(player.UserIDString))
                Message(player, "NoLongerQueued");
        }

        private void CommandLadder(BasePlayer player, string command, string[] args)
        {
            if (player == null) 
                return;

            bool life = Array.Exists(args, a => a.Contains("life", StringComparison.OrdinalIgnoreCase));
            using var ladder = GetPooledList<KeyValuePair<ulong, int>>();
            foreach (var (n, wins) in data.Get(life ? Points.Victory : Points.VictorySeed)) // build & sort
                if (ulong.TryParse(n, out var id))
                    ladder.Add(new(id, wins));

            if (ladder.Count < 30 && ConVar.Server.hostname.EndsWith("ed Test"))
            {
                for (int i = 0; i < 30 - ladder.Count; i++)
                {
                    var userid = (ulong)UnityEngine.Random.Range(1000, 9999999);
                    ladder.Add(new(userid, UnityEngine.Random.Range(15, 60)));
                }

                ladder.Insert(15, new(player.userID, 15));
            }

            ladder.Sort((a, b) => b.Value.CompareTo(a.Value)); // high-to-low

            Message(player, life ? "TopAll" : "Top", ladder.Count);
            int me = ladder.FindIndex(e => e.Key == player.userID); // -1 ⇒ never played

            for (int i = 0; i < ladder.Count; i++) // print top-10, plus the player's own row if it's outside the top-10
            {
                if (i >= 10 && i != me) continue;
                PrintRank(i + 1, ladder[i].Key, ladder[i].Value);
            }

            if (!life)
                Message(player, "LadderLife", szDuelChatCommand);

            void PrintRank(int rank, ulong id, int value)
            {
                string name = id == player.userID ? player.displayName : ConVar.Admin.GetPlayerName(id);
                int losses = data.Get(id.ToString(), life ? Points.Loss : Points.LossSeed);
                double ratio = losses > 0 ? Math.Round(value / (double)losses, 2) : value;
                Player.Message(player, msg("TopFormat", player.UserIDString, rank.ToString(), name, value, losses, ratio), id);
            }
        }

        private void CommandDuelist(IPlayer user, string command, string[] args)
        {
            var player = user.Object as BasePlayer;
            if (player != null && AimTrain.CanCall() && Convert.ToBoolean(AimTrain?.Call("IsAimTraining", (ulong)player.userID)))
                return;

            bool isAllowed = player != null && player.IsAdmin;
            if (IsEventBanned(user.Id))
            {
                Message(user, "Banned");
                return;
            }

            if (IsBlocked(user.Id))
            {
                Message(user, "SuicideBlock");
                return;
            }

            if (args.Contains("death_test"))
            {
                user.Message(msg("MatchDeathMessage1", user.Id, "nivex", "zada", ":rifle.ak:", "Head", 33.55));
                user.Message(msg("MatchDeathMessage2", user.Id, user.Name, data.Get(user.Id, Points.MatchSizeVictorySeed, 3), data.Get(user.Id, Points.MatchSizeLossSeed, 3), "zada", data.Get("1", Points.MatchSizeVictory, 3), data.Get("1", Points.MatchSizeVictory, 3), 3, GetWeapon(ItemManager.FindItemDefinition("rifle.ak"), "AK"), 35.33));
                user.Message(msg("DuelDeathMessage", user.Id, user.Name, 5, 1, "zada", 1, 5, 75.33, string.Empty));
                return;
            }

            if (args.Length >= 1 && args[0] == "ladder")
            {
                CommandLadder(player, command, args);
                return;
            }
            
            if (!data.DuelsEnabled)
            {
                if (!Array.Exists(args, arg => arg.ToLower() == "on"))
                    Message(user, "DuelsDisabled");

                if (!user.IsAdmin)
                    return;
            }

            bool noZone = data.Zones.Count == 0 || duelingZones.Count == 0;

            if (noZone)
            {
                if (!Array.Exists(args, arg => arg.ToLower() == "new") && !Array.Exists(args, arg => arg.ToLower() == "removeall") && !Array.Exists(args, arg => arg.ToLower() == "custom"))
                    Message(user, "NoZoneExists");

                if (!user.IsAdmin)
                    return;
            }

            if (!noZone && !data.DuelsEnabled && !Array.Exists(args, arg => arg.ToLower() == "on"))
                Message(user, "DuelsMustBeEnabled", szDuelChatCommand);

            bool isLimited = !user.IsAdmin && IsDueling(player);

            if (args.Length == 0)
            {
                Message(user, "HelpDuels", data.TotalDuels.ToString("N0"));
                Message(user, "ZoneNames", data.Zones.Count, string.Join(" ", data.Zones.Values.Take(10).Select(x => x.name)));

                if (!autoAllowAll)
                    Message(user, "HelpAllow", szDuelChatCommand);

                Message(user, "HelpBlock", szDuelChatCommand);
                Message(user, "HelpChallenge", szDuelChatCommand);
                Message(user, "HelpAccept", szDuelChatCommand);
                Message(user, "HelpCancel", szDuelChatCommand);
                Message(user, "HelpChat", szDuelChatCommand);
                Message(user, "HelpQueue", szQueueChatCommand);
                Message(user, "HelpLadder", szDuelChatCommand);
                Message(user, "HelpKit", szDuelChatCommand);

                if (allowBets)
                    Message(user, "HelpBet", szDuelChatCommand);

                if (tdmEnabled)
                    Message(user, "HelpTDM", szMatchChatCommand);

                Message(user, "UI_Help", szUIChatCommand);

                if (user.IsAdmin)
                {
                    Message(user, "HelpDuelAdmin", szDuelChatCommand);
                    Message(user, "HelpDuelAdminRefundAll", szDuelChatCommand);
                }

                return;
            }

            switch (args[0].ToLower())
            {
                case "leave":
                    {
                        LeaveEvent(player);
                        return;
                    }
                case "grid":
                    {
                        if (isAllowed)
                        {
                            if (_gridPositions.Count < 5000) _gridPositions.UnionWith(_gridPositionsVal);
                            foreach (var pos in _gridPositions)
                            {
                                if (player.Distance(pos) > 1000f) continue;
                                player.SendConsoleCommand("ddraw.text", 30f, Color.green, pos, "X");
                            }
                            ;
                        }
                        return;
                    }
                case "autoready":
                    {
                        ToggleAutoReady(player);
                        return;
                    }
                case "rematch":
                case "ready":
                    {
                        ReadyUp(player);
                        return;
                    }
                case "resetseed":
                    {
                        if (user.IsAdmin)
                        {
                            data.ResetSeed();
                            Message(user, "ResetSeed");
                            if (!user.IsServer) Puts("{0] ({1}): {2}", user.Name, user.Id, msg("ResetSeed", user.Id));
                        }
                        break;
                    }
                case "0":
                case "disable":
                case "off":
                    {
                        if (user.IsAdmin)
                        {
                            if (!data.DuelsEnabled)
                            {
                                Message(user, "DuelsDisabledAlready");
                                return;
                            }

                            data.DuelsEnabled = false;
                            Message(user, _duelists.Count > 0 ? "DuelsNowDisabled" : "DuelsNowDisabledEmpty");
                            SendDuelistsHome();
                            SendSpectatorsHome();
                            SaveData();
                        }
                        break;
                    }
                case "1":
                case "enable":
                case "on":
                    {
                        if (user.IsAdmin)
                        {
                            if (data.DuelsEnabled)
                            {
                                Message(user, "DuelsEnabledAlready");
                                return;
                            }

                            data.DuelsEnabled = true;
                            Message(user, "DuelsNowEnabled");
                            DuelAnnouncement(false);
                            SaveData();
                        }
                        break;
                    }
                case "custom":
                case "me":
                    {
                        if (isAllowed)
                        {
                            if (data.Zones.Count >= zoneAmount)
                            {
                                Message(user, "ZoneLimit", zoneAmount);
                                return;
                            }

                            if (Physics.Raycast(player.eyes.HeadRay(), out var hit, Mathf.Infinity, wallMask))
                            {
                                if (DuelTerritory(hit.point, 5f))
                                {
                                    Message(user, "ZoneExists");
                                    return;
                                }

                                float radius = zoneRadius;
                                foreach (var arg in args)
                                {
                                    if (float.TryParse(arg, out var r))
                                    {
                                        radius = r;
                                        break;
                                    }
                                }

                                var _nameArgs = args.Where(arg => arg.ToLower() != "tp" && arg != radius.ToString());
                                var name = _nameArgs.Count() > 0 ? string.Join(" ", _nameArgs) : null;
                                var zone = SetupDuelZone(hit.point, GetZoneName(name, radius));
                                int i = 0;

                                foreach (var spawn in zone.Spawns)
                                    player.SendConsoleCommand("ddraw.text", 30f, Color.yellow, spawn, ++i);

                                UpdateStability();

                                if (zoneCounter > 0) MessageB(player, $"Zone will reset after {zoneCounter} duels. Disable by setting `Create New Zone Every X Duels [0 = disabled]` to `0` in the config.");
                            }
                            else Message(player, "FailedRaycast");
                        }
                        break;
                    }
                case "remove":
                    {
                        if (isAllowed)
                        {
                            var zone = GetDuelZone(player.transform.position);
                            if (zone == null)
                            {
                                Message(user, "NoZoneFound");
                                return;
                            }

                            EjectPlayers(zone);
                            RemoveDuelZone(zone);
                            Message(user, "RemovedZone");
                        }
                        break;
                    }
                case "removeall":
                    {
                        if (user.IsAdmin)
                        {
                            if (duelingZones.Count > 0)
                            {
                                using var zones = GetPooledList(duelingZones);
                                foreach (var zone in zones)
                                {
                                    EjectPlayers(zone);
                                    Message(user, "RemovedZoneAt", zone.Location);
                                    RemoveDuelZone(zone);
                                }

                                data.Zones.Clear();
                                SaveData();
                            }
                            else Message(user, "NoZoneExists");
                        }
                        break;
                    }
                case "spawns":
                    {
                        if (isAllowed)
                        {
                            if (args.Length >= 2)
                            {
                                switch (args[1].ToLower())
                                {
                                    case "add":
                                        AddSpawnPoint(player, true);
                                        break;
                                    case "here":
                                        AddSpawnPoint(player, false);
                                        break;
                                    case "remove":
                                        RemoveSpawnPoint(player);
                                        break;
                                    case "removeall":
                                        RemoveSpawnPoints(player);
                                        break;
                                    case "wipe":
                                        WipeSpawnPoints(player);
                                        break;
                                    default:
                                        SendSpawnHelp(player);
                                        break;
                                }

                                return;
                            }

                            SendSpawnHelp(player);

                            int i = 0;
                            float dist = float.MaxValue;
                            DuelingZone destZone = null;

                            foreach (var zone in duelingZones)
                            {
                                if (zone.Distance(player.transform.position) > zone.ProtectionRadius + 200f)
                                    continue;

                                float distance = zone.Distance(player.transform.position);

                                if (distance < dist)
                                {
                                    dist = distance;
                                    destZone = zone;
                                }
                            }

                            if (destZone != null)
                                foreach (var spawn in destZone.Spawns)
                                    player.SendConsoleCommand("ddraw.text", 30f, Color.yellow, spawn, "<size=24>" + (++i) + "</size>");
                        }
                        break;
                    }
                case "rename":
                    {
                        if (isAllowed)
                        {
                            if (args.Length > 1)
                            {
                                var zone = GetDuelZone(player.transform.position);

                                if (zone == null || !data.Zones.TryGetValue(zone.Location, out var info))
                                {
                                    Message(user, "NoZoneFound");
                                    return;
                                }

                                info.name = string.Join(" ", args.Skip(1));
                                Message(user, "ZoneRenamed", info.name);
                            }
                            else Message(user, "ZoneRename", szDuelChatCommand);

                            return;
                        }
                        break;
                    }
                case "new":
                    {
                        if (user.IsAdmin)
                        {
                            if (data.Zones.Count >= zoneAmount)
                            {
                                Message(user, "ZoneLimit", zoneAmount);
                                return;
                            }

                            float radius = zoneRadius;
                            foreach (var arg in args)
                            {
                                if (float.TryParse(arg, out var r))
                                {
                                    radius = r;
                                    break;
                                }
                            }

                            var _nameArgs = args.Where(arg => arg.ToLower() != "tp" && arg != radius.ToString());
                            var name = _nameArgs.Count() > 0 ? string.Join(" ", _nameArgs) : null;
                            var zone = SetupDuelZone(GetZoneName(name, radius));

                            if (zone != null)
                            {
                                Message(user, "ZoneCreated");

                                if (player != null && Array.Exists(args, arg => arg.ToLower() == "tp"))
                                {
                                    Player.Teleport(player, zone.Location);
                                }
                            }
                        }
                        break;
                    }
                case "tpm":
                    {
                        if (isAllowed)
                        {
                            float dist = float.MaxValue;
                            var dest = Vector3.zero;
                            using var matches = GetPooledList(tdmMatches.Exists(m => m.IsStarted) ? tdmMatches.Where(m => m.IsStarted) : tdmMatches); // 0.1.17 if multiple zones then choose from active ones if any exist

                            foreach (var match in matches)
                            {
                                float distance = match.Zone.Distance(player.transform.position);

                                if (matches.Count > 1 && distance < match.Zone.ProtectionRadius * 4f) // move admin to the next nearest zone
                                    continue;

                                if (distance < dist)
                                {
                                    dist = distance;
                                    dest = match.Zone.Location;
                                }
                            }

                            if (dest != Vector3.zero)
                                Player.Teleport(player, dest);
                        }
                        break;
                    }
                case "tp":
                    {
                        if (isAllowed && duelingZones.Count > 0)
                        {
                            if (args.Length == 2 && int.TryParse(args[1], out int idx))
                            {
                                Player.Teleport(player, duelingZones[Math.Clamp(idx, 0, duelingZones.Count - 1)].Location);
                                return;
                            }

                            int currIdx = -1;
                            for (int i = 0; i < duelingZones.Count; i++)
                            {
                                DuelingZone z = duelingZones[i];
                                if (z.InRange(player.transform.position))
                                {
                                    currIdx = i;
                                    break;
                                }
                            }

                            int nextIdx = currIdx < 0 ? 0 : (currIdx + 1) % duelingZones.Count;
                            Player.Teleport(player, duelingZones[nextIdx].Location);
                            player.ChatMessage($"Teleported to zone {duelingZones[nextIdx].zoneName} @ {duelingZones[nextIdx].Location}");
                        }
                        break;
                    }
                case "save":
                    {
                        if (user.IsAdmin)
                        {
                            SaveData();
                            Message(user, "DataSaved");
                        }
                    }
                    break;
                case "ban":
                    {
                        if (user.IsAdmin && args.Length >= 2)
                        {
                            string targetId = args[1].IsSteamId() ? args[1] : BasePlayer.Find(args[1])?.UserIDString ?? null;

                            if (string.IsNullOrEmpty(targetId))
                            {
                                Message(user, "PlayerNotFound", args[1]);
                                return;
                            }

                            if (!data.Bans.ContainsKey(targetId))
                            {
                                data.Bans.Add(targetId, user.Id);
                                Message(user, "AddedBan", targetId);
                            }
                            else
                            {
                                data.Bans.Remove(targetId);
                                Message(user, "RemovedBan", targetId);
                            }

                            SaveData();
                        }
                        break;
                    }
                case "announce":
                    {
                        if (user.IsAdmin)
                            DuelAnnouncement(true);

                        break;
                    }
                case "claim":
                    {
                        if (isLimited || !player)
                        {
                            return;
                        }

                        if (!data.ClaimBets.TryGetValue(user.Id, out var claim))
                        {
                            Message(user, "NoBetsToClaim");
                            return;
                        }

                        using var bets = GetPooledList(claim);
                        foreach (var bet in bets)
                        {
                            var item = ItemManager.CreateByItemID(bet.itemid, bet.amount ?? 1);

                            if (item == null)
                                continue;

                            if (!item.MoveToContainer(player.inventory.containerMain, -1))
                            {
                                var position = player.transform.position;
                                item.Drop(position + new Vector3(0f, 1f, 0f) + position / 2f, (position + new Vector3(0f, 0.2f, 0f)) * 8f); // Credit: Slack comment by @visagalis
                            }

                            string message = msg("PlayerClaimedBet", user.Id, item.info.displayName.translated, item.amount);

                            MessageB(player, message);
                            Puts("{0} ({1}) - {2}", user.Name, user.Id, message);
                            claim.Remove(bet);

                            if (claim.Count == 0)
                            {
                                data.ClaimBets.Remove(user.Id);
                                Message(player, "AllBetsClaimed");
                            }
                        }
                        return;
                    }
                case "queue":
                case "que":
                case "q":
                    {
                        if (player != null && !IsDueling(player) && !string.IsNullOrEmpty(szQueueChatCommand))
                            CommandQueue(user, command, args);
                        return;
                    }
                case "chat":
                    {
                        if (broadcastDefeat)
                        {
                            if (!data.Chat.Contains(user.Id))
                                data.Chat.Add(user.Id);
                            else data.Chat.Remove(user.Id);

                            Message(user, data.Chat.Contains(user.Id) ? "DuelChatOff" : "DuelChatOn");
                        }
                        else
                        {
                            if (!data.ChatEx.Contains(user.Id))
                                data.ChatEx.Add(user.Id);
                            else data.ChatEx.Remove(user.Id);

                            Message(user, data.ChatEx.Contains(user.Id) ? "DuelChatOn" : "DuelChatOff");
                        }
                        return;
                    }
                case "kit":
                    {
                        if (isLimited || !player)
                        {
                            return;
                        }

                        string kits = string.Join(", ", VerifiedKits);

                        if (args.Length == 2 && !string.IsNullOrEmpty(kits))
                        {
                            string kit = GetVerifiedKit(args[1]); // Duel

                            if (!string.IsNullOrEmpty(kit))
                            {
                                data.CustomKits[user.Id] = kit;
                                Message(user, "KitSet", kit);
                            }
                            else
                                Message(user, "KitDoesntExist", args[1]);

                            return;
                        }

                        if (data.CustomKits.Remove(user.Id))
                        {
                            Message(user, "ResetKit");
                        }

                        if (string.IsNullOrEmpty(kits)) Message(user, "KitsNotConfigured");
                        else MessageB(player, kits);
                        return;
                    }
                case "allow":
                    {
                        if (isLimited)
                        {
                            return;
                        }

                        if (autoAllowAll)
                        {
                            Message(user, "PlayerRequestsAuto");
                            return;
                        }

                        if (!data.Allowed.Contains(user.Id))
                        {
                            data.Allowed.Add(user.Id);
                            Message(user, "PlayerRequestsOn");
                            return;
                        }

                        data.Allowed.Remove(user.Id);
                        Message(user, "PlayerRequestsOff");
                        RemoveRequests(player);
                        return;
                    }
                case "block":
                    {
                        if (args.Length >= 2)
                        {
                            var target = BasePlayer.Find(args[1]);

                            if (IsNull(target))
                            {
                                Message(user, "PlayerNotFound", args[1]);
                                return;
                            }

                            if (!data.BlockedUsers.TryGetValue(user.Id, out var block))
                            {
                                data.BlockedUsers.Add(user.Id, block = new());
                            }
                            else if (block.Contains(target.UserIDString))
                            {
                                block.Remove(target.UserIDString);

                                if (block.Count == 0)
                                    data.BlockedUsers.Remove(user.Id);

                                Message(user, "UnblockedRequestsFrom", target.displayName);
                                return;
                            }

                            block.Add(target.UserIDString);
                            Message(user, "BlockedRequestsFrom", target.displayName);
                            return;
                        }

                        if (!autoAllowAll && data.Allowed.Remove(user.Id))
                        {
                            Message(user, "PlayerRequestsOff");
                            RemoveRequests(player);
                            return;
                        }

                        Message(user, "AlreadyBlocked");
                        return;
                    }
                case "bet":
                    {
                        if (isLimited)
                        {
                            return;
                        }

                        if (!allowBets)
                        {
                            Message(user, "Betting is disabled.");
                            break;
                        }

                        if (duelingBets.Count == 0)
                        {
                            Message(user, "NoBetsConfigured");
                            return;
                        }

                        if (args.Length == 2)
                        {
                            switch (args[1].ToLower())
                            {
                                case "refundall":
                                    {
                                        if (user.IsAdmin)
                                        {
                                            if (data.Bets.Count == 0)
                                            {
                                                Message(user, "NoBetsToRefund");
                                                return;
                                            }

                                            using var bets = GetPooledList(data.Bets);
                                            foreach (var (userid, bet) in bets)
                                            {
                                                var target = BasePlayer.Find(userid);
                                                if (target == null) continue;

                                                Item item = ItemManager.CreateByItemID(bet.itemid, bet.amount ?? 1);
                                                if (item == null)
                                                    continue;

                                                if (!item.MoveToContainer(target.inventory.containerMain, -1, true) && !item.MoveToContainer(target.inventory.containerBelt, -1, true))
                                                {
                                                    item.Remove(0.01f);
                                                    continue;
                                                }

                                                Message(target, "RefundAllPlayerNotice", item.info.displayName.translated, item.amount);
                                                Message(player, "RefundAllAdminNotice", target.displayName, target.UserIDString, item.info.displayName.english, item.amount);
                                                data.Bets.Remove(userid);
                                            }

                                            if (data.Bets.Count > 0) Message(user, "BetsRemaining", data.Bets.Count);
                                            else Message(user, "AllBetsRefunded");
                                            SaveData();
                                            return;
                                        }

                                        break;
                                    }
                                case "forfeit":
                                    {
                                        if (allowBetRefund) // prevent operator error ;)
                                        {
                                            CommandDuelist(user, command, new[] { "bet", "refund" });
                                            return;
                                        }

                                        if (!allowBetForfeit)
                                        {
                                            Message(user, "CannotForfeit");
                                            return;
                                        }

                                        if (data.Bets.ContainsKey(user.Id))
                                        {
                                            if (HasRequest(user.Id))
                                            {
                                                Message(user, "CannotForfeitRequestDuel");
                                                return;
                                            }

                                            if (IsDuelist(user.Id))
                                            {
                                                Message(user, "CannotForfeitInDuel");
                                                return;
                                            }

                                            data.Bets.Remove(user.Id);
                                            Message(user, "BetForfeit");
                                            SaveData();
                                        }
                                        else Message(user, "NoBetToForfeit");

                                        return;
                                    }
                                case "cancel":
                                case "refund":
                                    {
                                        if (!allowBetRefund && !user.IsAdmin)
                                        {
                                            Message(user, "CannotRefund");
                                            return;
                                        }

                                        if (player != null && data.Bets.ContainsKey(user.Id))
                                        {
                                            if (HasRequest(user.Id))
                                            {
                                                Message(user, "CannotRefundRequestDuel");
                                                return;
                                            }

                                            if (IsDuelist(user.Id))
                                            {
                                                Message(user, "CannotRefundInDuel");
                                                return;
                                            }

                                            var bet = data.Bets[user.Id];

                                            Item item = ItemManager.CreateByItemID(bet.itemid, bet.amount ?? 1);

                                            if (!item.MoveToContainer(player.inventory.containerMain, -1, true))
                                            {
                                                if (!item.MoveToContainer(player.inventory.containerBelt, -1, true))
                                                {
                                                    var position = player.transform.position;
                                                    item.Drop(position + new Vector3(0f, 1f, 0f) + position / 2f, (position + new Vector3(0f, 0.2f, 0f)) * 8f); // Credit: Slack comment by @visagalis
                                                }
                                            }

                                            data.Bets.Remove(user.Id);
                                            Message(user, "BetRefunded");
                                            SaveData();
                                        }
                                        else Message(user, "NoBetToRefund");

                                        return;
                                    }
                                default:
                                    break;
                            }
                        }

                        if (data.Bets.TryGetValue(user.Id, out var b))
                        {
                            Message(user, "AlreadyBetting", b.trigger, b.amount);
                            if (allowBetRefund) Message(user, "ToRefundUse", szDuelChatCommand);
                            else if (allowBetForfeit) Message(user, "ToForfeitUse", szDuelChatCommand);

                            return;
                        }

                        if (args.Length < 3)
                        {
                            Message(user, "AvailableBets");

                            foreach (var betInfo in duelingBets)
                                Message(user, $"{betInfo.trigger} (max: {betInfo.max})");

                            Message(user, "BetSyntax", szDuelChatCommand);
                            return;
                        }

                        if (!int.TryParse(args[2], out var betAmount))
                        {
                            Message(user, "InvalidNumber", args[2]);
                            return;
                        }

                        if (betAmount > 500 && betAmount % 500 != 0)
                        {
                            Message(user, "MultiplesOnly");
                            return;
                        }

                        if (player != null)
                        {
                            foreach (var betInfo in duelingBets)
                            {
                                if (betInfo.trigger.ToLower() == args[1].ToLower())
                                {
                                    CreateBet(player, betAmount, betInfo);
                                    return;
                                }
                            }
                        }

                        Message(user, "InvalidBet", args[1]);
                        return;
                    }
                case "accept":
                case "a":
                case "y":
                case "yes":
                    {
                        if (isLimited || !player)
                        {
                            return;
                        }

                        if (!DuelsEnabled(user.Id))
                        {
                            Message(user, "MustAllowDuels", szDuelChatCommand);
                            return;
                        }

                        if (IsParticipant(player))
                        {
                            Message(user, "AlreadyDueling");
                            return;
                        }

                        if (!GetPendingRequest(user.Id, out var request))
                        {
                            Message(user, "NoRequestsReceived");
                            return;
                        }

                        if (!IsNewman(player))
                        {
                            Message(user, "MustBeNaked");
                            return;
                        }

                        BasePlayer target = request.Key.GetPlayer();
                        if (target == null || !target.IsConnected)
                        {
                            Message(user, "DuelCancelledFor", request.Key.Name);
                            dataRequests.Remove(request.Key);
                            return;
                        }

                        if (!IsNewman(target))
                        {
                            Message(user, "TargetMustBeNaked");
                            Message(target, "MustBeNaked");
                            return;
                        }

                        data.Restricted.Remove(user.Id);
                        data.Restricted.Remove(target.UserIDString);

                        if (!SelectZone(player, target, false))
                        {
                            Message(player, "AllZonesFull", duelingZones.Count, playersPerZone);
                            Message(target, "AllZonesFull", duelingZones.Count, playersPerZone);
                        }

                        return;
                    }
                case "cancel":
                case "decline":
                    {
                        if (!player) return;
                        if (IsDueling(player))
                        {
                            LeaveEvent(player);
                            return;
                        }
                        else if (GetRequest(user.Id, out var request))
                        {
                            if (request.Key.ID != user.Id)
                                Message(request.Key.Player, "DuelCancelledWith", user.Name);
                            else Message(request.Value.Player, "DuelCancelledWith", user.Name);

                            Message(user, "DuelCancelComplete");
                            dataRequests.Remove(request.Key);
                            return;
                        }

                        Message(user, "NoPendingRequests");
                        return;
                    }
                default:
                    {
                        if (user.IsServer)
                        {
                            user.Reply(string.Format("{0} on|off|new|removeall|resetseed", szDuelChatCommand));
                            return;
                        }

                        if (isLimited)
                        {
                            return;
                        }

                        if (!DuelsEnabled(user.Id))
                        {
                            Message(user, "MustAllowDuels", szDuelChatCommand);
                            return;
                        }

                        if (IsDueling(player))
                        {
                            Message(user, "AlreadyDueling");
                            return;
                        }

                        if (data.Restricted.Contains(user.Id) && !user.IsAdmin)
                        {
                            Message(user, "MustWaitToRequestAgain", 1);
                            return;
                        }

                        if (!IsNewman(player))
                        {
                            Message(user, "MustBeNaked");
                            return;
                        }

                        var target = BasePlayer.Find(args[0]);

                        if (target == null || target == player) //if (target == null || (target == player && target.userID != 76561198212544308))
                        {
                            Message(user, "PlayerNotFound", args[0]);
                            return;
                        }

                        if (data.BlockedUsers.ContainsKey(target.UserIDString) && data.BlockedUsers[target.UserIDString].Contains(user.Id))
                        {
                            Message(user, "CannotRequestThisPlayer");
                            return;
                        }

                        if (IsDueling(target))
                        {
                            Message(user, "TargetAlreadyDueling", target.displayName);
                            return;
                        }

                        if (!DuelsEnabled(target.UserIDString))
                        {
                            Message(user, "NotAllowedYet", target.displayName, szDuelChatCommand);
                            return;
                        }

                        if (GetInitiatedRequest(user.Id, out var request))
                        {
                            Message(user, "MustWaitForAccept", request.Value.Name);
                            return;
                        }

                        if (GetPendingRequest(target.UserIDString, out request))
                        {
                            Message(user, "PendingRequestAlready");
                            return;
                        }

                        if (data.Bets.ContainsKey(user.Id) && !data.Bets.ContainsKey(target.UserIDString))
                        {
                            var bet = data.Bets[user.Id];

                            Message(user, "TargetHasNoBet", target.displayName);
                            Message(user, "YourBet", bet.trigger, bet.amount);
                            return;
                        }

                        if (data.Bets.ContainsKey(target.UserIDString) && !data.Bets.ContainsKey(user.Id))
                        {
                            var targetBet = data.Bets[target.UserIDString];
                            Message(user, "MustHaveSameBet", target.displayName, targetBet.trigger, targetBet.amount);
                            return;
                        }

                        if (data.Bets.ContainsKey(user.Id) && data.Bets.ContainsKey(target.UserIDString))
                        {
                            var playerBet = data.Bets[user.Id];
                            var targetBet = data.Bets[target.UserIDString];

                            if (!playerBet.Equals(targetBet))
                            {
                                Message(user, "BetsDoNotMatch", playerBet.trigger, playerBet.amount, targetBet.trigger, targetBet.amount);
                                return;
                            }
                        }

                        if (args.Length > 1)
                            SetPlayerZone(player, args.Skip(1));

                        PlayerData playerData = new(player);
                        PlayerData targetData = new(target);
                        dataRequests[playerData] = targetData;
                        Message(target, "DuelRequestReceived", player.displayName, szDuelChatCommand);
                        Message(player, "DuelRequestSent", target.displayName, szDuelChatCommand);

                        if (RemoveFromQueue(user.Id))
                            Message(user, "RemovedFromQueueRequest");

                        if (!data.Restricted.Contains(playerData.ID))
                            data.Restricted.Add(playerData.ID);

                        timer.In(60f, () =>
                        {
                            data.Restricted.Remove(playerData.ID);

                            if (dataRequests.Remove(playerData))
                            {
                                if (player != null && !IsDueling(player))
                                    Message(user, "RequestTimedOut", targetData.Name);
                            }
                        });

                        break;
                    }
            } // end switch
        }

        public bool GetRequest(string id, out KeyValuePair<PlayerData, PlayerData> request) { foreach (var pair in dataRequests) { if (pair.Key.ID == id || pair.Value.ID == id) { request = pair; return true; } } request = default; return false; }
        public bool HasRequest(string id) { foreach (var pair in dataRequests) { if (pair.Key.ID == id || pair.Value.ID == id) { return true; } } return false; }
        public bool GetInitiatedRequest(string id, out KeyValuePair<PlayerData, PlayerData> request) { foreach (var pair in dataRequests) { if (pair.Key.ID == id) { request = pair; return true; } } request = default; return false; }
        public bool GetPendingRequest(string id, out KeyValuePair<PlayerData, PlayerData> request) { foreach (var pair in dataRequests) { if (pair.Value.ID == id) { request = pair; return true; } } request = default; return false; }
        public bool HasPendingRequest(string id) { foreach (var pair in dataRequests) { if (pair.Value.ID == id) { return true; } } return false; }

        private static bool IsZoneEmpty(DuelingZone z, int min) => z != null && !z.IsFinito && z.TotalPlayers == 0 && !z.IsLocked && z.Spawns.Count >= min;

        private static bool IsZoneAvailable(DuelingZone z, int min, int max) => z != null && !z.IsFinito && !z.IsFull && !z.IsLocked && z.Spawns.Count >= min && z.Spawns.Count <= max;

        private static bool IsNull(BaseNetworkable a) => a == null || a.IsDestroyed;

        private static bool IsConnected(BasePlayer a) => !IsNotConnected(a);

        private static bool IsNotConnected(BasePlayer a)
        {
            if (a == null || a.IsDestroyed) return true;
            if (a is DuelistNPC) return false;
            return !a.IsConnected;
        }

        private void SafelyHeal(BaseCombatEntity entity)
        {
            entity.Invoke(() =>
            {
                if (entity != null && !entity.IsDestroyed)
                {
                    entity.Heal(entity.MaxHealth());
                }
            }, 0.1f);
        }

        public void CancelDamage(HitInfo hitInfo)
        {
            if (hitInfo != null && hitInfo.damageTypes != null)
            {
                hitInfo.damageTypes.Clear();
                hitInfo.DidHit = false;
                hitInfo.DoHitEffects = false;
            }
        }

        private void DestroyAll()
        {
            using var zones = GetPooledList(duelingZones);
            foreach (var zone in zones)
            {
                UnityEngine.Object.Destroy(zone.gameObject);
            }
        }

        private void InitializeDefinitions()
        {
            foreach (var def in ItemManager.GetItemDefinitions())
            {
                if (def.TryGetComponent(out ItemModDeployable mod))
                {
                    _deployables[mod.entityPrefab.resourcePath] = def;
                }
            }
        }
        public void SaveData()
        {
            if (data != null)
            {
                Interface.Oxide.DataFileSystem.WriteObject(Name, data);
            }
        }

        private void TryAddDisconnect(string uid)
        {
            if (_disconnected.Contains(uid))
            {
                return;
            }
            if (_trackers.Remove(uid, out var obj))
            {
                obj.DestroyMe();
            }
            _disconnected.Add(uid);
            timer.Once(60f, () => _disconnected.Remove(uid));
        }

        private void TryAddSuicide(string uid)
        {
            if (!_suicide.Contains(uid))
            {
                _suicide.Add(uid);
                timer.Once(60f, () => _suicide.Remove(uid));
            }
        }

        public void SetEscapedEventTracker(BasePlayer player, bool enable, bool duel)
        {
            if (enable && !_trackers.TryGetValue(player.UserIDString, out var tracker))
            {
                tracker = player.gameObject.AddComponent<EscapedEventTracker>();
                tracker.Init(player, this, duel);
                _trackers[player.UserIDString] = tracker;
            }
            else if (!enable && _trackers.Remove(player.UserIDString, out tracker))
            {
                UnityEngine.Object.Destroy(tracker);
            }
        }

        private bool IsBlocked(string uid) => _suicide.Contains(uid) || _disconnected.Contains(uid);

        private bool IsExploiting(BasePlayer player, bool duel)
        {
            if (player is DuelistNPC)
            {
                return false;
            }

            if (AimTrain.CanCall() && Convert.ToBoolean(AimTrain?.Call("IsAimTraining", (ulong)player.userID)))
            {
                AimTrain?.Call("LeaveAimTrain", player);
                DestroyUI(player);

                if (duel)
                {
                    OnDuelistLost(player, true, false);
                    RemoveDuelist(player.UserIDString);
                    ResetDuelist(player.UserIDString, false);
                    EndSpectate(player);
                    SendHome(player);
                }
                else if (GetDeathmatch(player, out var match))
                {
                    if (!match.IsStarted && match.EitherEmpty)
                    {
                        match.End();
                    }

                    if (match.IsStarted && !match.IsOver)
                    {
                        DefeatMessage(player, match);
                        match.RoundsLeft.Remove(player.UserIDString);
                        match.CanRematch = false;
                        match.RemoveMatchPlayer(player);
                    }
                }

                return true;
            }

            return false;
        }

        public void SubscribeHooks(bool flag) // we're using lots of temporary and permanent hooks so we'll turn off the temporary hooks when the plugin is loaded, and unsubscribe to others inside of their hooks when they're no longer in use
        {
            if (!flag)
            {
                Unsubscribe(nameof(OnPlayerDisconnected));
                Unsubscribe(nameof(CanNetworkTo));
                Unsubscribe(nameof(OnItemDropped));
                Unsubscribe(nameof(OnPlayerSleepEnded));
                Unsubscribe(nameof(CanCreateWorldProjectile));
                Unsubscribe(nameof(CanLootEntity));
                Unsubscribe(nameof(OnPlayerRespawned));
                Unsubscribe(nameof(OnEntityTakeDamage));
                Unsubscribe(nameof(OnEntitySpawned));
                Unsubscribe(nameof(CanBuild));
                Unsubscribe(nameof(OnPlayerHealthChange));
                Unsubscribe(nameof(OnEntityDeath));
                Unsubscribe(nameof(OnEntityKill));
                //Unsubscribe(nameof(OnPlayerCommand));
                Unsubscribe(nameof(OnPlayerConnected));
                Unsubscribe(nameof(OnRestoreUponDeath));
                Unsubscribe(nameof(CanRevivePlayer));
                Unsubscribe(nameof(OnLifeSupportSavingLife));
                return;
            }

            Subscribe(nameof(OnPlayerDisconnected));
            Subscribe(nameof(OnItemDropped));
            Subscribe(nameof(OnPlayerSleepEnded));
            Subscribe(nameof(CanCreateWorldProjectile));
            Subscribe(nameof(CanLootEntity));
            Subscribe(nameof(OnEntitySpawned));
            Subscribe(nameof(OnRestoreUponDeath));
            Subscribe(nameof(CanRevivePlayer));
            Subscribe(nameof(OnLifeSupportSavingLife));

            if (!allowPlayerDeaths)
                Subscribe(nameof(OnPlayerHealthChange));

            Subscribe(nameof(OnEntityTakeDamage));
            Subscribe(nameof(OnEntityDeath));

            if (useBlacklistCommands || useWhitelistCommands)
                Subscribe(nameof(OnPlayerCommand));

            if (respawnWalls)
                Subscribe(nameof(OnEntityKill));
        }

        private void FillDeathmatchNpcQueue(BasePlayer player)
        {
            DuelingZone zone = duelingZones.Find(x => IsZoneAvailable(x, 1, 999));
            if (zone == null)
            {
                player.ChatMessage("No zone found");
                return;
            }

            var target = SpawnNpc(player.transform.position);
            if (target == null)
            {
                player.ChatMessage("Target failed to spawn");
                return;
            }

            zone.npcs.Add(target);
            var match = SetupTeams(player, target);
            if (match == null)
            {
                player.ChatMessage("No match found");
                return;
            }

            match.TeamSize = maxDeathmatchSize;
            Vector3 pos = zone.Location;

            for (int i = 0; i < (match.TeamSize * 2) - 2; i++)
            {
                var npc = SpawnNpc(pos);
                if (npc == null)
                {
                    continue;
                }

                zone.npcs.Add(target);
                if (!match.IsFull(Team.Good))
                {
                    match.AddMatchPlayer(npc, Team.Good);
                    continue;
                }

                if (!match.IsFull(Team.Evil))
                {
                    match.AddMatchPlayer(npc, Team.Evil);
                    continue;
                }

                ulong userid = npc.userID;
                BasePlayer.bots.Remove(npc);
                npc.DelayedSafeKill();
                BasePlayer.freeBotIds.Remove(userid);
            }
        }

        private static ulong BotIdCounter = 554922525;

        private DuelistNPC SpawnNpc(Vector3 pos)
        {
            if (!InstantiateEntity(new(), pos, true, out var brain, out var npc))
            {
                return null;
            }

            ulong userid = BotIdCounter++;

            npc.userID = userid;
            npc.UserIDString = userid.ToString();
            brain.displayName = RandomUsernames.Get(userid);
            npc.displayName = npc.DisplayNameOverride = brain.displayName;

            npc.loadouts = Array.Empty<PlayerInventoryProperties>();
            npc.Spawn();
            npc.CancelInvoke(npc.EquipTest);
            BasePlayer.bots.Remove(npc);

            return npc;
        }

        private bool InstantiateEntity(List<Vector3> wander, Vector3 position, bool isStationary, out DuelistBrain brain, out DuelistNPC npc)
        {
            static void CopySerializableFields<T>(T src, T dst)
            {
                var srcFields = typeof(T).GetFields();
                foreach (var field in srcFields)
                {
                    if (field.IsStatic) continue;
                    object value = field.GetValue(src);
                    field.SetValue(dst, value);
                }
            }

            var prefabName = "assets/rust.ai/agents/npcplayer/humannpc/scientist/scientistnpc_heavy.prefab";
            var prefab = GameManager.server.FindPrefab(prefabName);
            var go = Facepunch.Instantiate.GameObject(prefab, position, Quaternion.identity);

            go.SetActive(false);

            go.name = prefabName;

            ScientistBrain scientistBrain = go.GetComponent<ScientistBrain>();
            ScientistNPC scientistNpc = go.GetComponent<ScientistNPC>();

            npc = go.AddComponent<DuelistNPC>();
            brain = go.AddComponent<DuelistBrain>();
            brain.Instance = this;
            brain._baseEntity = npc;
            brain.npc = npc;
            brain.states ??= new();
            npc.Brain = brain;

            CopySerializableFields(scientistNpc, npc);
            UnityEngine.Object.DestroyImmediate(scientistBrain, true);
            UnityEngine.Object.DestroyImmediate(scientistNpc, true);
            UnityEngine.SceneManagement.SceneManager.MoveGameObjectToScene(go, Rust.Server.EntityScene);

            go.SetActive(true);

            return npc != null;
        }

        private void OnDuelistLost(BasePlayer victim, bool sendHome, bool ready)
        {
            RemoveEntities(victim.userID);
            string vicId = victim.UserIDString;
            bool isVicNpc = victim is NPCPlayer;

            if (!_duelists.TryGetValue(vicId, out var attack))
            {
                NextTick(() => SendHome(victim));
                return;
            }

            BasePlayer attacker = attack.GetPlayer();
            string atkName = attack.Name;
            string atkId = attack.ID;
            bool isAtk = attacker != null;
            bool isAtkNpc = isAtk && attacker is NPCPlayer;
            double atkHealth = isAtk ? Math.Round(attacker.health, 2) : 0;

            dataDeath.Remove(vicId); // remove them from automatic deaths
            dataDeath.Remove(atkId);
            _duelists.Remove(vicId); // unset their status as duelers
            _duelists.Remove(atkId);
            victim.inventory.Strip();
            Metabolize(victim, false);
            SetEscapedEventTracker(victim, false, true);

            data.TotalDuels++;
            data.Add(vicId, Points.Loss);
            data.Add(atkId, Points.Victory);
            int vicLossesSeed = data.Add(vicId, Points.LossSeed);
            int atkLossesSeed = data.Get(atkId, Points.LossSeed);
            int vicVictoriesSeed = data.Get(vicId, Points.VictorySeed);
            int atkVictoriesSeed = data.Add(atkId, Points.VictorySeed);
            BetInfo bet = !isVicNpc && !isAtkNpc && data.Bets.TryGetValue(atkId, out var v3) && data.Bets.TryGetValue(vicId, out var v4) && v3.Equals(v4) && !IsAllied(victim, attacker) ? v3 : null; // victim bet his attacker and lost, use later to add a claim for the attacker

            Puts(RemoveFormatting(msg("DuelDeathMessage", null, atkName, atkVictoriesSeed, atkLossesSeed, victim.displayName, vicVictoriesSeed, vicLossesSeed, atkHealth, GetBetWon(bet)))); // send message to console
            Interface.CallHook("OnDuelistDefeated", attacker, victim);

            if (guiAnnounceUITime > 0f)
            {
                if (sendDefeatedHome)
                {
                    announcements[vicId] = msg("DuelDeathMessage", vicId, atkName, atkVictoriesSeed, atkLossesSeed, victim.displayName, vicVictoriesSeed, vicLossesSeed, atkHealth, GetBetWon(bet, vicId));
                    announcements[atkId] = msg("DuelDeathMessage", atkId, atkName, atkVictoriesSeed, atkLossesSeed, victim.displayName, vicVictoriesSeed, vicLossesSeed, atkHealth, GetBetWon(bet, atkId));
                }
                else
                {
                    CreateAnnouncementUI(victim, msg("DuelDeathMessage", vicId, atkName, atkVictoriesSeed, atkLossesSeed, victim.displayName, vicVictoriesSeed, vicLossesSeed, atkHealth, GetBetWon(bet, vicId)));
                    CreateAnnouncementUI(attacker, msg("DuelDeathMessage", atkId, atkName, atkVictoriesSeed, atkLossesSeed, victim.displayName, vicVictoriesSeed, vicLossesSeed, atkHealth, GetBetWon(bet, atkId)));
                }
            }

            using var targets = GetPlayerList();
            foreach (var target in targets)
            {
                if (target != victim && target != attacker && data.Chat.Contains(target.UserIDString))
                    continue;

                if (!broadcastDefeat && target != victim && target != attacker && !data.ChatEx.Contains(target.UserIDString))
                    continue;

                Message(target, "DuelDeathMessage", atkName, atkVictoriesSeed, atkLossesSeed, victim.displayName, vicVictoriesSeed, vicLossesSeed, atkHealth, GetBetWon(bet, target.UserIDString));
            }

            if (isAtk && bet != null) // award the bet to the attacker
            {
                if (!data.ClaimBets.TryGetValue(atkId, out var bets))
                    data.ClaimBets.Add(atkId, bets = new());

                bets.Add(new(bet.amount * 2, bet.trigger, 0, bet.itemid));
                data.Bets.Remove(atkId);
                data.Bets.Remove(vicId);
                Puts(msg("ConsoleBetWon", null, attacker.displayName, attacker.UserIDString, victim.displayName, vicId));
                Message(attacker, "NotifyBetWon", szDuelChatCommand);
            }

            ulong atkIdU = Convert.ToUInt64(atkId);
            var atkZone = RemoveDuelist(atkId);
            RemoveEntities(atkIdU);
            AwardPlayer(atkId, economicsMoney, serverRewardsPoints);

            Interface.Oxide.CallHook("DisableBypass", (ulong)victim.userID);
            Interface.Oxide.CallHook("DisableBypass", atkIdU);

            if (isAtk)
            {
                attacker.inventory.Strip();
                Metabolize(attacker, false);
                SetEscapedEventTracker(attacker, false, true);
            }

            var vicZone = RemoveDuelist(vicId);
            atkZone ??= vicZone;
            TryRelocateZone(atkZone);

            if (!AnyParticipants())
                Unsubscribe(nameof(OnPlayerHealthChange));

            bool isBlocked = IsBlocked(vicId);
            if (sendHome || isBlocked)
            {
                NextTick(() =>
                {
                    SendHome(attacker);
                    SendHome(victim);
                });

                if (isBlocked)
                    return;
            }

            if (attacker != null && ready)
            {
                if (victim.IsConnected && attacker.IsConnected)
                {
                    var rematch = new Rematch(this);
                    rematches.Add(rematch);
                    rematch.Duelists.Add(attacker);
                    rematch.Duelists.Add(victim);
                    rematch.ReadyCheck();
                }

                if (!sendHome && !IsParticipant(attacker) && !IsParticipant(victim))
                {
                    StartSpectate(attacker);
                    StartSpectate(victim);
                }
            }
        }

        private void TryRelocateZone(DuelingZone zone) // TODO: needs to be a coroutine
        {
            // nothing to do if we don’t have a zone, no counter set, or it’s already finished
            if (zone == null || zoneCounter <= 0 || zone.IsFinito)
                return;

            // count this duel; bail if we haven’t hit the threshold yet
            if (++zone.Kills < zoneCounter)
                return;

            // mark this zone as done
            zone.IsFinito = true;

            // only relocate when it’s empty
            if (zone.TotalPlayers > 0)
                return;

            // x amount of duels completed. time to relocate and start all over! changing the dueling zones location keeps things mixed up and entertaining for everyone. especially to shift terrain advantages
            RemoveDuelZone(zone);
            SetupDuelZone(GetZoneName(null, zoneRadius));
            SaveData();
        }

        private void DefeatMessage(BasePlayer victim, GoodVersusEvilMatch match)
        {
            if (tdmAttackers.Remove(victim.UserIDString, out var info))
            {
                if (tdmServerDeaths || data.ChatEx.Count > 0)
                {
                    using var targets = GetPlayerList();
                    foreach (var target in targets)
                    {
                        if (data.Chat.Contains(target.UserIDString) && target != victim)
                            continue;

                        //Message(target, GetMatchDefeatMessage(victim, info));
                        Message(target, GetMatchDeathMessage(target, victim, info, match.TeamSize));
                    }
                }
                else if (tdmMatchDeaths)
                {
                    using var targets = match.GetAllPlayers();
                    foreach (var target in targets)
                    {
                        if (data.Chat.Contains(target.UserIDString) && target != victim)
                            continue;

                        //Message(target, GetMatchDefeatMessage(victim, info));
                        Message(target, GetMatchDeathMessage(target, victim, info, match.TeamSize));
                    }
                }

                if (guiAnnounceUITime > 0f)
                {
                    if (match.SendDefeatedHome(victim.UserIDString))
                    {
                        //announcements[victim.UserIDString] = GetMatchDefeatMessage(victim, info);
                        announcements[victim.UserIDString] = GetMatchDeathMessage(victim, victim, info, match.TeamSize);
                    }
                    else
                    {
                        //CreateAnnouncementUI(victim, GetMatchDefeatMessage(victim, info));
                        CreateAnnouncementUI(victim, GetMatchDeathMessage(victim, victim, info, match.TeamSize));
                    }
                }

                UpdateMatchStats(victim.UserIDString, Points.MatchDeath);
                UpdateMatchStats(info.AttackerId, Points.MatchKill);
            }
        }

        private static string Abbr(string name)
        {
            if (string.IsNullOrEmpty(name)) 
                return string.Empty;
            int len = name.Length;
            char[] buf = new char[len];
            int pos = 0;
            for (int i = 0; i < len; i++)
            {
                char c = name[i];
                if ((c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9'))
                    buf[pos++] = c;
            }
            return pos == len ? name : new string(buf, 0, pos);
        }

        private static string GetWeapon(ItemDefinition def, string defaultValue)
        {
            if (def == null)
            {
                return Abbr(defaultValue);
            }
            return ":" + def.shortname + ":";
        }

        private string GetMatchDefeatMessage(BasePlayer victim, AttackerInfo info) => 
            msg("MatchDeathMessage1", victim.UserIDString, info.AttackerName, victim.displayName, GetWeapon(info.def, info.Weapon), info.BoneName, info.Distance);
        
        private string GetMatchDeathMessage2(BasePlayer target, BasePlayer victim, AttackerInfo info, int size) => msg("MatchDeathMessage2", target.UserIDString,
                info.AttackerName, data.Get(info.AttackerId, Points.MatchSizeVictorySeed, size), data.Get(info.AttackerId, Points.MatchSizeLossSeed, size),
                victim.displayName, data.Get(victim.UserIDString, Points.MatchSizeVictory, size), data.Get(victim.UserIDString, Points.MatchSizeVictory, size), size, GetWeapon(info.def, info.Weapon), info.Distance);

        private string GetMatchDeathMessage(BasePlayer target, BasePlayer victim, AttackerInfo info, int size)
        {
            using var sb = DisposableBuilder.Get();
            return sb.Append(msg("MatchDeathMessage2", target.UserIDString))
                .Replace("{AttackerName}", info.AttackerName)
                .Replace("{AttackerWins}", data.Get(info.AttackerId, Points.MatchSizeVictorySeed, size).ToString())
                .Replace("{AttackerLosses}", data.Get(info.AttackerId, Points.MatchSizeLossSeed, size).ToString())
                .Replace("{VictimName}", victim.displayName)
                .Replace("{VictimWins}", data.Get(victim.UserIDString, Points.MatchSizeVictorySeed, size).ToString())
                .Replace("{VictimLosses}", data.Get(victim.UserIDString, Points.MatchSizeLossSeed, size).ToString())
                .Replace("{Size}", size.ToString())
                .Replace("{Weapon}", GetWeapon(info.def, info.Weapon))
                .Replace("{Distance}", info.Distance).ToString();
        }

        private string GetBetWon(BetInfo bet, string id = null)
        {
            return bet != null ? msg("BetWon", id, bet.trigger, bet.amount) : string.Empty;
        }

        public DuelZoneInfo GetZoneName(string name, float radius)
        {
            if (string.IsNullOrEmpty(name))
            {
                name = (data.Zones.Count + 1).ToString();
            }
            return new(name, radius);
        }

        public void SendDuelistsHome()
        {
            using var targets = GetPlayerList(true);
            foreach (var target in targets)
            {
                if (data.Homes.ContainsKey(target.UserIDString) && DuelTerritory(target.transform.position))
                {
                    target.inventory.Strip();
                    if (target is DuelistNPC)
                    {
                        target.DelayedSafeKill();
                    }
                    else SendHome(target);
                }
                if (IsDuelist(target.UserIDString))
                {
                    ResetDuelist(target.UserIDString);
                }
            }
        }

        public void SendSpectatorsHome()
        {
            using var targets = GetPlayerList(true);
            foreach (var target in targets)
            {
                if (IsSpectating(target))
                {
                    EndSpectate(target);
                }
            }
        }

        private void StartSpectate(BasePlayer player)
        {
            if (IsNotConnected(player))
                return;

            if (!IsParticipant(player))
            {
                SendHome(player);
                return;
            }

            if (player is DuelistNPC)
            {
                player.inventory.Strip();
                player.health = 100f;
                StopBleeding(player);
                player.StopWounded();
                Disappear(player);
                return;
            }

            if (!player.CanInteract())
            {
                if (player.IsDead())
                {
                    spectators.Add(player.UserIDString);
                    player.RespawnAt(player.transform.position, Quaternion.identity);
                }
                timer.Once(1f, () => StartSpectate(player));
                return;
            }

            spectators.Add(player.UserIDString);
            Message(player, "BeginSpectating");
            player.inventory.Strip();
            player.health = 100f;
            StopBleeding(player);
            player.StopWounded();
            CreateDefeatUI(player);
            Disappear(player);
        }

        private void EndSpectate(BasePlayer player)
        {
            CuiHelper.DestroyUi(player, "DuelistUI_Defeat");
            Reappear(player);

            if (spectators.Remove(player.UserIDString))
            {
                if (playerHealth > 0f && player.IsAlive())
                    player.health = playerHealth;

                player.SendNetworkUpdate();
                Message(player, "EndSpectating");
            }
        }

        public void SetPlayerTime(BasePlayer player, bool set)
        {
            if (!setPlayerTime || !set && !_times.Remove(player.userID))
            {
                return;
            }

            var time = set ? "12" : "-1";

            ConsoleSystem.Run(ConsoleSystem.Option.Server.Quiet(), $"setenv {player.UserIDString} time {time}");

            if (set) _times.Add(player.userID);
        }

        public bool SetPlayerZone(BasePlayer player, string[] args)
        {
            foreach (string arg in args)
            {
                foreach (var z in duelingZones)
                {
                    if (z.name.Equals(arg, StringComparison.OrdinalIgnoreCase))
                    {
                        playerZones[player.UserIDString] = z;
                        Message(player, "ZoneSet", z.name);
                        return true;
                    }
                }
            }
            return false;
        }

        public GoodVersusEvilMatch SetupTeams(BasePlayer player, BasePlayer target)
        {
            if (!IsNewman(player))
            {
                Message(player, "MustBeNaked");
                Message(target, "DuelMustBeNaked", player.displayName);
                return null;
            }

            if (!IsNewman(target))
            {
                Message(target, "MustBeNaked");
                Message(player, "DuelMustBeNaked", target.displayName);
                return null;
            }

            RemoveFromQueue(player.UserIDString);
            RemoveFromQueue(target.UserIDString);

            var match = new GoodVersusEvilMatch(this);
            match.Setup(player, target);

            SubscribeHooks(true);
            return match;
        }

        public void CheckAutoReady(BasePlayer player)
        {
            if (autoReady || data.AutoReady.Contains(player.UserIDString))
            {
                if (!readyUiList.Contains(player.UserIDString))
                {
                    ToggleReadyUI(player);
                }
            }
            else if (readyUiList.Contains(player.UserIDString))
            {
                CuiHelper.DestroyUi(player, "DuelistUI_Ready");
                readyUiList.Remove(player.UserIDString);
            }
        }

        public void ToggleAutoReady(BasePlayer player)
        {
            if (player == null)
                return;

            if (!autoReady)
            {
                if (!data.AutoReady.Remove(player.UserIDString))
                    data.AutoReady.Add(player.UserIDString);

                Message(player, data.AutoReady.Contains(player.UserIDString) ? "RematchAutoOn" : "RematchAutoOff");
            }

            if (DuelTerritory(player.transform.position))
                CreateDefeatUI(player);

            if (duelistUI.Contains(player.UserIDString))
                RefreshUI(player);
        }

        public void ReadyUp(BasePlayer player)
        {
            if (player == null)
                return;

            Rematch rematch = null;
            foreach (var x in rematches)
            {
                if (x.HasPlayer(player))
                {
                    rematch = x;
                    break;
                }
            }

            if (rematch == null)
            {
                ToggleAutoReady(player);
                //if (IsSpectating(player)) Message(player, "RematchNone");
                return;
            }

            if (rematch.Ready.Contains(player))
            {
                Message(player, "RematchAcceptedAlready");
                ToggleAutoReady(player);
            }
            else
            {
                Message(player, "RematchAccepted");
                rematch.Ready.Add(player);
            }

            if (rematch.IsReady())
            {
                rematch.Start();
                rematches.Remove(rematch);
            }
        }

        private void ResetTemporaryData() // keep our datafile cleaned up by removing entries which are temporary
        {
            if (data == null)
                data = new();

            _duelists.Clear();
            dataRequests.Clear();
            _immune.Clear();
            data.Restricted.Clear();
            dataDeath.Clear();
            Queued.Clear();
            data.Homes.Clear();
            data.Kits.Clear();
            SaveData();
        }

        public DuelingZone RemoveDuelist(string playerId)
        {
            foreach (var zone in duelingZones)
            {
                if (zone.HasPlayer(playerId))
                {
                    zone.RemovePlayer(playerId);
                    return zone;
                }
            }

            return null;
        }

        public static void HolsterWeapon(BasePlayer player)
        {
            //HeldEntity heldEntity = player.GetHeldEntity();
            //if (heldEntity != null)
            //{
            //    heldEntity.SetHeld(true);
            //}
        }

        public void ResetDuelist(string targetId, bool removeHome = true) // remove a dueler from the datafile
        {
            data.Kits.Remove(targetId);
            data.Restricted.Remove(targetId);
            _immune.Remove(targetId);
            _duelists.Remove(targetId);
            dataDeath.Remove(targetId);

            if (GetInitiatedRequest(targetId, out var request))
                dataRequests.Remove(request.Key);

            if (removeHome)
                data.Homes.Remove(targetId);

            if (duelingZones.Count > 0)
                RemoveDuelist(targetId);

            RemoveFromQueue(targetId);
        }

        private void RemoveZeroStats() // someone enabled duels but never joined one. remove them to keep the datafile cleaned up
        {
            data.Allowed.RemoveAll(targetId =>
            {
                if (data.Get(targetId, Points.Loss) == 0 && data.Get(targetId, Points.Victory) == 0) // no permanent stats
                {
                    ResetDuelist(targetId);
                    return true;
                }
                return false;
            });
        }

        public void SetupManagedZones()
        {
            ManagedZones.Clear();

            if (!ZoneManager.CanCall())
            {
                return;
            }

            timer.Once(30f, SetupManagedZones);
            config.Zones.Allowed.RemoveAll(string.IsNullOrWhiteSpace);

            if (config.Zones.Allowed.Contains("*"))
            {
                return;
            }

            var zoneIds = ZoneManager?.Call("GetZoneIDs") as string[];

            if (zoneIds == null || zoneIds.Length == 0)
            {
                return;
            }

            foreach (string zoneId in zoneIds)
            {
                var obj = ZoneManager?.Call("ZoneFieldList", zoneId);
                if (obj == null || obj is not Dictionary<string, string> dict)
                    continue;

                var zoneLoc = dict.TryGetValue("Location", out var loc) ? loc.ToVector3() : Vector3.zero;
                var radius = dict.TryGetValue("radius", out var rad) ? Convert.ToSingle(rad) : 0f;
                var size = dict.TryGetValue("size", out var sz) ? sz.ToVector3() : Vector3.zero;

                if (zoneLoc == Vector3.zero || (radius <= 0 && size == Vector3.zero))
                    continue;

                var zoneName = dict.TryGetValue("name", out var n) ? n : null;
                var zoneRot = dict.TryGetValue("rotation", out var rot) ? Quaternion.Euler(rot.ToVector3()) : Quaternion.identity;
                var isBlocked = !config.Zones.Allowed.Exists(zone => zone == zoneId || (!string.IsNullOrEmpty(zoneName) && zoneName.Equals(zone, StringComparison.OrdinalIgnoreCase)));
                ManagedZones[zoneId] = new(zoneId, zoneLoc, zoneRot, radius, size, isBlocked, zoneRadius);
            }
        }

        public void SetupDuelZones()
        {
            if (data.Zones.Count > zoneAmount) // zoneAmount was changed in the config file so remove existing zones until we're at the new cap
            {
                do
                {
                    var (zonePos, zone) = data.Zones.FirstOrDefault();

                    if (spAutoRemove && data.Spawns.Count > 0)
                    {
                        using var spawns = GetPooledList(data.Spawns);
                        foreach (var spawn in spawns)
                            if (Vector3.Distance(spawn, zonePos) <= zone.radius)
                                data.Spawns.Remove(spawn);
                    }

                    data.AutoGeneratedSpawns.Remove(zonePos);
                    data.Zones.Remove(zonePos);
                } while (data.Zones.Count > zoneAmount);
            }

            foreach (var entry in data.Zones.ToList()) // create all zones that don't already exist
                SetupDuelZone(entry.Key, entry.Value);

            if (autoSetup && data.Zones.Count < zoneAmount) // create each dueling zone that is missing. if this fails then console will be notified
            {
                int attempts = Math.Max(zoneAmount, 5); // 0.1.10 fix - infinite loop fix for when zone radius is too large to fit on the map
                int created = 0;

                do
                {
                    if (SetupDuelZone(GetZoneName(null, zoneRadius)) != null)
                        created++;
                } while (data.Zones.Count < zoneAmount && --attempts > 0);

                if (attempts <= 0)
                {
                    if (created > 0)
                        Puts(msg("SupportCreated", null, created));
                    else
                        Puts(msg("SupportInvalidConfig"));
                }
            }

            if (duelingZones.Count > 0)
                Puts(msg("ZonesSetup", null, duelingZones.Count));
        }

        public DuelingZone SetupDuelZone(DuelZoneInfo zone) // starts the process of creating a new or existing zone and then setting up it's own spawn points around the circumference of the zone
        {
            float radius = zone.radius;
            Vector3 zonePos = Vector3.zero;
            DateTime tick = DateTime.Now; // create a timestamp to see how long this process takes
            int maxRetries = 2000; // 0.1.9: increased due to rock collider detection. 0.1.10 rock collider detection removed but amount not changed. 1.3.6 rewrite to cache beforehand
            int retries = maxRetries; // servers with high entity counts will require this

            if (ManagedZones.Count == 0 && ZoneManager.CanCall())
                SetupManagedZones();

            do
            {
                var currentPos = RandomDropPosition();

                if (currentPos == Vector3.zero)
                    continue;

                if (DuelTerritory(currentPos, radius + 15f)) // check if position overlaps an existing zone
                {
                    _gridPositions.Remove(currentPos);
                    continue; // overlaps, retry.
                }

                if (IsManagedZone(currentPos))
                    continue;

                using var positions = GetCircumferencePositions(currentPos, radius - 15f, 1f, 0f); // gather positions around the proposed zone
                float min = 200f;
                float max = -200f;
                int water = 0;

                foreach (var pos in positions)
                {
                    if (Physics.Raycast(new Vector3(pos.x, pos.y + 100f, pos.z), Vector3.down, 500f, Layers.Mask.Water)) //look for water
                        water++; // count the amount of water colliders

                    min = Mathf.Min(pos.y, min); // set the lowest and highest points of the terrain
                    max = Mathf.Max(pos.y, max);
                }

                if (max - min > maxIncline || currentPos.y - min > maxIncline) // the incline is too steep to be suitable for a dueling zone, retry.
                {
                    _gridPositions.Remove(currentPos);
                    continue;
                }

                if (water > positions.Count / 4) // too much water, retry.
                {
                    _gridPositions.Remove(currentPos);
                    continue;
                }

                using var entities = GetPooledList<BaseEntity>();
                Vis.Entities(currentPos, radius + 100f, entities, blockedMask, QueryTriggerInteraction.Ignore); // get all entities using the provided layermask
                entities.RemoveAll(x => x.IsNpc || x is NPCPlayer || x is BaseOven || x is SleepingBag || x is IceFence || x is SimpleBuildingBlock || x.OwnerID == 0 && x is not BasePlayer);

                if (entities.Count > 0) // if any entities were found from the blockedMask then we don't want this as our dueling zone. retry.
                {
                    _gridPositions.Remove(currentPos);
                    continue;
                }

                positions.Clear();

                if (currentPos != Vector3.zero)
                    zonePos = currentPos;
            } while (zonePos == Vector3.zero && --retries > 0); // prevent infinite loops

            if (zonePos != Vector3.zero)
            {
                int tries = maxRetries - retries + 1;
                string foundZone = msg("FoundZone", null, tries, (DateTime.Now - tick).TotalMilliseconds);
                Puts(tries == 1 ? foundZone.Replace("tries", "try") : foundZone); // we found a dueling zone! return the position to be assigned, spawn the zone and the spawn points!
            }

            if (zonePos == Vector3.zero) // unfortunately we weren't able to find a location. this is likely due to an extremely high entity count. just try again.
                return null;

            return SetupDuelZone(zonePos, zone);
        }

        public DuelingZone SetupDuelZone(Vector3 zonePos, DuelZoneInfo zone)
        {
            zonePos = zonePos.SnapTo(0.001f);
            if (!data.Zones.ContainsKey(zonePos))
                data.Zones[zonePos] = zone;

            var go = new GameObject();
            var newZone = go.AddComponent<DuelingZone>();
            newZone.zoneName = zone.name;
            newZone.env = this;
            newZone.go = go;
            newZone.ProtectionRadius = Mathf.Clamp(zone.radius, 50f, 300f);
            newZone.SqrProtectionRadius = newZone.ProtectionRadius * newZone.ProtectionRadius;
            newZone.Setup(zonePos);
            duelingZones.Add(newZone);

            if (duelingZones.Count == 1)
            {
                if (blockSpawning) Subscribe(nameof(OnPlayerRespawned));
                Subscribe(nameof(OnEntityTakeDamage));
                Subscribe(nameof(OnEntitySpawned));
                Subscribe(nameof(CanBuild));
            }

            newZone.CreateZoneWalls(newZone.Location, zone.radius - 5f, zoneUseWoodenWalls ? hewwPrefab : heswPrefab);
            return newZone;
        }

        public void EjectPlayers(DuelingZone zone)
        {
            using var players = zone.Players;
            foreach (var player in players)
            {
                EjectPlayer(player);
            }
        }

        public void EjectPlayer(BasePlayer player)
        {
            if (IsNull(player) || player is DuelistNPC)
                return;

            player.inventory.Strip();
            ResetDuelist(player.UserIDString, false);
            SendHome(player);
        }

        public void RemoveDuelZone(DuelingZone zone)
        {
            var uid = zone.Location;
            foreach (var npc in zone.npcs)
                npc.SafelyKill();

            using var ids = GetPooledList(spectators);
            foreach (string playerId in ids)
            {
                var player = BasePlayer.Find(playerId);

                if (player == null)
                {
                    spectators.Remove(playerId);
                    continue;
                }

                if (zone.Distance(player.transform.position) <= zone.ProtectionRadius)
                {
                    EndSpectate(player);
                    SendHome(player);
                }
            }

            var match = tdmMatches.FirstOrDefault(x => x.Zone != null && x.Zone == zone);

            if (match != null)
            {
                match.IsOver = true;
                match.End();
            }

            if (spAutoRemove && data.Spawns.Count > 0)
                foreach (var spawn in zone.Spawns)
                    data.Spawns.Remove(spawn);

            data.Zones.Remove(uid);
            data.AutoGeneratedSpawns.Remove(uid);

            RemoveEntities(zone);
            zone.Kill();

            if (duelingZones.Count == 0 && tdmMatches.Count == 0)
            {
                SubscribeHooks(false);
                CheckZoneHooks();
            }
        }

        public void RemoveEntities(ulong userId)
        {
            if (duelEntities.Remove(userId, out var ents))
            {
                for (int i = 0, n = ents.Count; i < n; i++)
                {
                    ents[i].SafelyKill();
                }
            }
        }

        public void RemoveEntities(DuelingZone zone)
        {
            using var tmp = GetPooledList(duelEntities);
            foreach (var (userid, entities) in tmp)
            {
                for (int i = entities.Count - 1; i >= 0; i--)
                {
                    var e = entities[i];
                    if (e.IsKilled())
                    {
                        entities.RemoveAt(i);
                        continue;
                    }
                    var v = e.transform.position - zone.Location;
                    if (v.sqrMagnitude <= zone.SqrProtectionRadius + 2f)
                    {
                        entities.RemoveAt(i);
                        e.Kill();
                    }
                }
                if (entities.Count == 0)
                {
                    duelEntities.Remove(userid);
                }
            }
        }

        public DuelingZone GetDuelZone(Vector3 startPos, float offset = 1f)
        {
            offset *= offset;
            foreach (var zone in duelingZones)
            {
                if (zone.SqrDistance(startPos) <= zone.SqrProtectionRadius + offset)
                {
                    return zone;
                }
            }
            return null;
        }

        public void SendHome(BasePlayer player) // send a player home to the saved location that they joined from
        {
            if (player != null && player.IsHuman() && data.Homes.TryGetValue(player.UserIDString, out var homePos))
            {
                if (player.IsDead() && !player.IsConnected && !respawnDeadDisconnect)
                {
                    data.Homes.Remove(player.UserIDString);
                    return;
                }

                if (player.IsSleeping() || player.HasPlayerFlag(BasePlayer.PlayerFlags.ReceivingSnapshot))
                {
                    timer.Once(2f, () => SendHome(player));
                    return;
                }

                
                RemoveEntities(player.userID);

                if (DuelTerritory(homePos) && !player.IsAdmin)
                {
                    using var bags = GetPooledList(SleepingBag.FindForPlayer(player.userID, true));

                    if (bags.Count > 0)
                    {
                        bags.Sort((x, y) => x.net.ID.Value.CompareTo(y.net.ID.Value));
                        homePos = bags[0].transform.position;
                        homePos.y += 0.25f;
                    }
                    else
                    {
                        homePos = ServerMgr.FindSpawnPoint().pos;
                    }
                }

                if (player.IsDead())
                {
                    if (sendDeadHome)
                        player.RespawnAt(homePos, default);
                    else player.Respawn();
                }
                else
                {
                    if (!sendDeadHome)
                    {
                        player.LifeStoryEnd();
                        player.Respawn();
                    }
                    else Teleport(player, homePos);
                }

                if (playerHealth > 0f)
                    player.health = playerHealth;

                StopBleeding(player);
                Reappear(player);
                GiveRespawnLoot(player);
                data.Homes.Remove(player.UserIDString);

                if (guiAutoEnable || createUI.Contains(player.UserIDString))
                    OnPlayerConnected(player);

                if (readyUiList.Contains(player.UserIDString))
                    ToggleReadyUI(player);
            }
        }

        public void GiveRespawnLoot(BasePlayer player)
        {
            if (respawnLoot.Count > 0)
            {
                player.inventory.Strip();

                foreach (var entry in respawnLoot)
                {
                    ItemDefinition def = ItemManager.FindItemDefinition(entry.shortname);
                    if (def == null) continue;
                    ulong skin = RequiresOwnership(def, entry.skin) ? 0 : entry.skin;
                    Item item = ItemManager.CreateByName(entry.shortname, entry.amount, skin);
                    var container = entry.container == "wear" ? player.inventory.containerWear : entry.container == "belt" ? player.inventory.containerBelt : player.inventory.containerMain;
                    if (item != null && !item.MoveToContainer(container, entry.slot) && !player.inventory.GiveItem(item))
                    {
                        item.Remove(0.01f);
                    }
                }
            }
            else if (!string.IsNullOrEmpty(autoKitName) && Kits.CanCall() && IsKit(autoKitName))
            {
                player.inventory.Strip();
                Kits.Call("GiveKit", player, autoKitName);
            }
            else plugins.Find("Loadoutless")?.Call("OnPlayerRespawned", player);
        }

        private void UpdateStability()
        {
            if (noStability)
            {
                Subscribe(nameof(OnEntitySpawned));

                using var ents = GetPooledList(BaseNetworkable.serverEntities);
                foreach (var ent in ents)
                {
                    var block = ent as BuildingBlock;
                    if (block == null || block.grounded || !DuelTerritory(block.transform.position))
                        continue;

                    if (block.OwnerID == 0 || permission.UserHasGroup(block.OwnerID.ToString(), "admin"))
                        block.grounded = true;
                }
            }
        }

        public void SetupPower(BaseEntity e)
        {
            if (e == null || e.IsDestroyed)
            {
                return;
            }
            else if (autoOvens && e is BaseOven)
            {
                e.SetFlag(BaseEntity.Flags.On, true);
            }
            else if (autoFlames && e is FlameTurret ft)
            {
                if (!ft.HasFuel())
                {
                    ft.inventory.AddItem(ItemManager.FindItemDefinition("lowgradefuel"), 5);
                }

                ft.fuelPerSec = 0f;
            }
            else if (autoTurrets && e is AutoTurret at)
            {
                at.InitiateStartup();
                at.SetPeacekeepermode(false);
            }
        }

        private void CheckZoneHooks()
        {
            if (respawnWalls && duelingZones.Count > 0)
            {
                Subscribe(nameof(OnEntityDeath));
                Subscribe(nameof(OnEntityKill));
            }
        }

        private void CheckDuelistMortality()
        {
            if (_immune.Count > 0) // each player that spawns into a dueling zone is given immunity for X seconds. here we'll keep track of this and remove their immunities
            {
                var timeStamp = Time.time;
                using var immunities = GetPooledList(_immune);
                foreach (var immune in immunities)
                {
                    var player = immune.Value.GetPlayer();
                    var time = immune.Value.Time - timeStamp;

                    if (time <= 0)
                    {
                        _immune.Remove(immune.Key);

                        if (IsNotConnected(player))
                            continue;

                        CuiHelper.DestroyUi(player, "DuelistUI_Countdown");
                        Message(player, "ImmunityFaded");
                    }
                    else if (player != null && player.IsConnected)
                    {
                        if (noMovement && _immune.TryGetValue(player.UserIDString, out var dest))
                        {
                            player.Teleport(dest.Spawn);
                        }

                        CreateCountdownUI(player, time);
                    }
                }
            }

            if (dataDeath.Count > 0) // keep track of how long the match has been going on for, and if it's been too long then kill the player off.
            {
                var timeStamp = Time.time;
                using var deaths = GetPooledList(dataDeath);
                foreach (var death in deaths)
                {
                    if (death.Value - timeStamp <= 0)
                    {
                        var target = BasePlayer.Find(death.Key);
                        dataDeath.Remove(death.Key);

                        if (!InEvent(target))
                            continue;

                        target.inventory.Strip();
                        OnEntityDeath(target, null);
                    }
                }
            }

            UpdateMatchUI();
        }

        // API & Helper methods
        private static PooledList<BasePlayer> GetPlayerList(bool sleepers = false)
        {
            PooledList<BasePlayer> players = GetPooledList<BasePlayer>();
            foreach (var player in BasePlayer.activePlayerList)
            {
                if (player != null && player.displayName != null)
                {
                    players.Add(player);
                }
            }
            if (!sleepers)
            {
                return players;
            }
            foreach (var player in BasePlayer.sleepingPlayerList)
            {
                if (player != null && player.displayName != null)
                {
                    players.Add(player);
                }
            }
            return players;
        }

        private float ClosestDistanceSq(Vector3 position)
        {
            float closestDistSq = float.MaxValue;

            foreach (var zone in duelingZones)
            {
                float distSq = (zone.Location - position).sqrMagnitude;
                if (distSq < closestDistSq)
                    closestDistSq = distSq;
            }

            return closestDistSq;
        }

        public static bool IsCustomEntity(BaseEntity m) => m.PrefabName.StartsWith("assets/custom/");

        private static float MaxTerrainY = 150f;
        private static float GetSpawnHeight(Vector3 v, float maxSpawnY)
        {
            float y = Mathf.Max(TerrainMeta.HeightMap.GetHeight(v), TerrainMeta.WaterMap.GetHeight(v));
            MaxTerrainY = Mathf.Max(MaxTerrainY, y);
            Ray ray = new Ray(new Vector3(v.x, Mathf.Min(MaxTerrainY, maxSpawnY) + 12f, v.z), Vector3.down);
            if (GamePhysics.Trace(ray, 0f, out RaycastHit hit, Mathf.Infinity, 144802049, QueryTriggerInteraction.Ignore))
                return Mathf.Max(y, hit.point.y);
            return y;
        }

        [HookMethod("DuelistTerritory")]
        public bool DuelTerritory(Vector3 position, float offset = 5f) // 0.1.21: arena can be inside of the zone at any height
        {
            position.y = 0f;
            offset *= offset;
            foreach (var zone in duelingZones)
            {
                if ((zone.LocationXZ3D - position).sqrMagnitude <= zone.SqrProtectionRadius + offset)
                {
                    return true;
                }
            }
            return false;
        }

        private void GetAllPlayersNonAlloc(List<BasePlayer> duelers)
        {
            foreach (var duelist in _duelists.Values)
            {
                if (duelist.Player != null)
                {
                    duelers.Add(duelist.Player);
                }
            }
            foreach (var team in tdmMatches)
            {
                using var players = team.GetAllPlayers();
                foreach (var player in players)
                {
                    duelers.Add(player);
                }
            }
        }

        private void GetAllPlayersNonAlloc(List<string> duelers)
        {
            duelers.AddRange(_duelists.Keys);
            foreach (var team in tdmMatches)
            {
                foreach (var player in team.Good.Players.Keys)
                {
                    duelers.Add(player);
                }
                foreach (var player in team.Evil.Players.Keys)
                {
                    duelers.Add(player);
                }
            }
        }

        private bool GetMatchRequestTarget(BasePlayer sender, out string targetId) => tdmRequests.TryGetValue(sender.UserIDString, out targetId);

        private bool GetMatchRequestSender(BasePlayer recipient, out string senderId)
        {
            foreach (var entry in tdmRequests)
            {
                if (entry.Value == recipient.UserIDString)
                {
                    senderId = entry.Key;
                    return true;
                }
            }
            senderId = null;
            return false;
        }

        private bool HasRequestTarget(BasePlayer sender) => GetMatchRequestTarget(sender, out _);

        private bool HasRequestSender(BasePlayer recipient) => GetMatchRequestSender(recipient, out _);

        private bool ImmunityEnabled() => immunityTime >= 1;

        private bool UserHasImmunity(string userid) => ImmunityEnabled() && _immune.TryGetValue(userid, out var immune) && immune.Time > Time.time;

        public void EnableUserImmunity(BasePlayer player, Vector3 spawn)
        {
            if (ImmunityEnabled())
            {
                _immune[player.UserIDString] = new(player, Time.time + immunityTime, spawn);
            }
        }

        private bool DuelsEnabled(string userid) => autoAllowAll || data.Allowed.Contains(userid);

        private bool AnyParticipants(bool spectator = false)
        {
            if (spectator && spectators.Count > 0) return true;
            return _duelists.Count > 0 || tdmMatches.Count > 0;
        }

        private bool IsParticipant(BasePlayer player, bool spectator = false)
        {
            if (player == null || player.IsDestroyed) return false;
            return IsParticipant(player.UserIDString, spectator);
        }

        private bool IsParticipant(string userid, bool spectator = false)
        {
            if (spectator && IsSpectator(userid)) return true;
            return IsDuelist(userid) || IsTeamMember(userid);
        }

        private bool IsDuelist(string userid)
        {
            return _duelists.ContainsKey(userid);
        }

        [HookMethod("inEvent")]
        private bool InEvent(BasePlayer player, bool spectate = false)
        {
            if (player == null || player.IsDestroyed) return false;
            if (IsParticipant(player.UserIDString)) return DuelTerritory(player.transform.position);
            return spectate && IsSpectator(player.UserIDString) && DuelTerritory(player.transform.position);
        }

        private bool IsDueling(BasePlayer player)
        {
            return player != null && !player.IsDestroyed && IsDuelist(player.UserIDString) && DuelTerritory(player.transform.position);
        }

        private bool GetDuelist(BasePlayer player, out PlayerData playerData)
        {
            playerData = null;
            return player != null && !player.IsDestroyed && _duelists.TryGetValue(player.UserIDString, out playerData) && DuelTerritory(player.transform.position);
        }

        private bool InDeathmatch(BasePlayer player)
        {
            return IsTeamMember(player) && DuelTerritory(player.transform.position);
        }

        private bool IsTeamMember(BasePlayer player)
        {
            return player != null && !player.IsDestroyed && IsTeamMember(player.UserIDString);
        }

        private bool IsTeamMember(string userid)
        {
            foreach (var match in tdmMatches)
            {
                if (match.GetTeam(userid) != Team.None)
                {
                    return true;
                }
            }
            return false;
        }

        public bool GetDeathmatch(BasePlayer player, out GoodVersusEvilMatch match)
        {
            match = null;
            if (player == null || player.IsDestroyed)
            {
                return false;
            }
            foreach (var m in tdmMatches)
            {
                if (m.GetTeam(player) != Team.None)
                {
                    match = m;
                    break;
                }
            }
            return match != null && DuelTerritory(player.transform.position);
        }

        private bool IsSpectator(BasePlayer player)
        {
            return player != null && !player.IsDestroyed && IsSpectator(player.UserIDString);
        }

        private bool IsSpectator(string userid)
        {
            return spectators.Contains(userid);
        }

        private bool IsSpectating(BasePlayer player)
        {
            return IsSpectator(player) && DuelTerritory(player.transform.position);
        }

        private bool IsEventBanned(string targetId)
        {
            return data.Bans.ContainsKey(targetId);
        }

        public void Log(string file, string message, bool timestamp = false)
        {
            LogToFile(file, message, this, false, timestamp);
        }

        public bool IsOnConstruction(Vector3 position)
        {
            position.y += 1f;
            return Physics.Raycast(position, Vector3.down, out var hit, 1.5f, constructionMask) && hit.GetEntity() != null;
        }

        public bool Teleport(BasePlayer player, Vector3 destination, float radius = 0f, bool sleep = true)
        {
            if (player == null || destination == Vector3.zero) // don't send a player to their death. this should never happen
                return false;

            player.Invoke(player.EndLooting, 0.01f);

            if (DuelTerritory(destination))
            {
                foreach (var rematch in rematches)
                {
                    if (rematch.HasPlayer(player))
                    {
                        rematches.Remove(rematch);
                        break;
                    }
                }

                SetPlayerTime(player, true);
            }

            if (player.IsWounded())
                player.StopWounded();

            if (playerHealth > 6f)
                player.health = playerHealth;

            if (sleep && player.IsConnected)
                player.StartSleeping();

            if (player.IsConnected && (Vector3.Distance(player.transform.position, destination) > radius * 2f || !DuelTerritory(destination))) // 1.1.2 reduced from 150 to 100
            {
                player.SetPlayerFlag(BasePlayer.PlayerFlags.ReceivingSnapshot, true);
                player.ClientRPC(RpcTarget.Player("StartLoading", player), arg1: true);
                player.UpdateNetworkGroup();
                player.SendEntityUpdate();
            }

            player.Teleport(destination);
            player.SendNetworkUpdateImmediate();
            StopBleeding(player);

            if (LustyMap.CanCall())
            {
                LustyMap?.Call(DuelTerritory(destination) ? "DisableMaps" : "EnableMaps", player);
            }

            if (!sleep && player.IsConnected || player is DuelistNPC)
                OnPlayerSleepEnded(player);

            return true;
        }

        private static void StopBleeding(BasePlayer player)
        {
            player.metabolism.bleeding.value = 0;
            player.metabolism.isDirty = true;
            player.metabolism.SendChanges();
        }

        public bool IsThrownWeapon(Item item)
        {
            if (item == null)
                return false;

            if (item.info.category == ItemCategory.Weapon || item.info.category == ItemCategory.Tool)
            {
                if (item.info.stackable > 1)
                    return false;

                var weapon = item?.GetHeldEntity() as BaseProjectile;

                if (weapon == null)
                    return true;

                if (weapon.primaryMagazine.capacity > 0)
                    return false;
            }

            return false;
        }

        private HashSet<Vector3> _gridPositions = new(), _gridPositionsVal = new();

        public Vector3 RandomDropPosition()
        {
            if (_gridPositions.Count == 0)
            {
                SetupPositions();
                _gridPositionsVal.UnionWith(_gridPositions);
            }

            if (_gridPositions.Count < 1000)
            {
                _gridPositions.Clear();
                _gridPositions.UnionWith(_gridPositionsVal);
            }

            return _gridPositions.ElementAt(Random.Range(0, _gridPositions.Count));
        }

        private void SetupPositions()
        {
            _gridPositions.Clear();
            int minPos = (int)(World.Size / -2f);
            int maxPos = (int)(World.Size / 2f);
            float maxRadius = config.Zones.zoneRadius;

            for (float x = minPos; x < maxPos; x += 15f)
            {
                for (float z = minPos; z < maxPos; z += 15f)
                {
                    var pos = new Vector3(x, 0f, z);

                    if (IsMonumentPosition(pos))
                        continue;

                    if (IsManagedZone(pos))
                        continue;

                    var y = TerrainMeta.HeightMap.GetHeight(pos);
                    pos.y = y + 100f; // setup the hit

                    if (!Physics.Raycast(pos, Vector3.down, out var hit, pos.y, groundMask))
                        continue; // found water instead of land

                    if (WaterLevel.GetOverallWaterDepth(pos, true, true, null) > 0f)
                        continue;

                    if ((ContainsTopology(TerrainTopology.Enum.Road | TerrainTopology.Enum.Roadside, pos, maxRadius) || HasPointOnPathList(TerrainMeta.Path?.Roads, pos, maxRadius)))
                        continue;

                    if ((ContainsTopology(TerrainTopology.Enum.Rail | TerrainTopology.Enum.Railside, pos, maxRadius) || HasPointOnPathList(TerrainMeta.Path?.Rails, pos, maxRadius)))
                        continue;

                    pos.y = Mathf.Max(hit.point.y, y); // get the max height

                    _gridPositions.Add(pos);
                }
            }
        }

        private bool IsMonumentPosition(Vector3 pos)
        {
            foreach (var monument in monuments)
            {
                if ((monument.Key - pos).sqrMagnitude < monument.Value) // don't put the dueling zone inside of a monument. players will throw a shit fit
                {
                    return true;
                }
            }

            return false;
        }

        public bool IsManagedZone(Vector3 v)
        {
            if (ManagedZones.Count > 0)
            {
                foreach (var zone in ManagedZones.Values)
                {
                    if (zone.IsPositionInZone(v))
                    {
                        return zone.IsBlocked; // blocked by zone manager
                    }
                }
            }
            return false;
        }

        public bool ContainsTopology(TerrainTopology.Enum mask, Vector3 position, float radius)
        {
            return (TerrainMeta.TopologyMap.GetTopology(position, radius) & (int)mask) != 0;
        }

        public bool HasPointOnPathList(List<PathList> paths, Vector3 point, float radius)
        {
            return !paths.IsNullOrEmpty() && paths.Exists(path => path?.Path?.Points?.Exists(p => InRange(point, p, radius)) ?? false);
        }

        public static bool InRange2D(Vector3 a, Vector3 b, float distance)
        {
            return (a - b).SqrMagnitude2D() <= distance * distance;
        }

        public static bool InRange(Vector3 a, Vector3 b, float distance)
        {
            return (a - b).sqrMagnitude <= distance * distance;
        }

        public PooledList<Vector3> GetCircumferencePositions(Vector3 center, float radius, float next, float y) // as the name implies
        {
            var positions = GetPooledList<Vector3>();
            float degree = 0f;

            while (degree < 360)
            {
                float angle = (float)(2 * Math.PI / 360) * degree;
                float x = center.x + radius * (float)Math.Cos(angle);
                float z = center.z + radius * (float)Math.Sin(angle);
                var position = new Vector3(x, 0f, z);

                position.y = y == 0f ? TerrainMeta.HeightMap.GetHeight(position) : y;
                positions.Add(position);

                degree += next;
            }

            return positions;
        }

        public List<Vector3> GetAutoSpawns(DuelingZone zone)
        {
            var spawns = new List<Vector3>();
            var key = zone.Location;

            if (data.AutoGeneratedSpawns.TryGetValue(key, out var value) && value.Count > 0)
                spawns.AddRange(value); // use cached spawn points

            if (!data.AutoGeneratedSpawns.ContainsKey(key))
                data.AutoGeneratedSpawns.Add(key, new());

            if (spawns.Count < 2)
                spawns = CreateSpawnPoints(zone.Location, zone.ProtectionRadius); // create spawn points on the fly

            data.AutoGeneratedSpawns[key] = new(spawns);
            return spawns;
        }

        public List<Vector3> CreateSpawnPoints(Vector3 center, float radius)
        {
            var positions = new List<Vector3>(); // 0.1.1 bugfix: spawn point height (y) wasn't being modified when indexing the below foreach list. instead, create a copy of each position and return a new list (cause: can't modify members of value types without changing the collection and invalidating the enumerator. bug: index the value type and change the value. result: list did not propagate)

            // create spawn points slightly inside of the dueling zone so they don't spawn inside of walls
            using var vectors = GetCircumferencePositions(center, radius - 15f, 5f, 0f);
            foreach (var v in vectors)
            {
                Vector3 pos = new(v.x, 0f, v.z);
                pos.y = GetSpawnHeight(pos, center.y + radius); // 1.3.6 rewrite
                if (ValidSpawnPoint(pos))
                {
                    pos.y += 0.75f;
                    positions.Add(pos);
                }
            }

            return positions;
        }

        private bool ValidSpawnPoint(Vector3 spawnPos)
        {
            if (avoidWaterSpawns && WaterLevel.GetWaterDepth(spawnPos, true, true, null) > 0.6f)
                return false; // 0.1.16 / 1.3.6: better method to check water level

            if (GamePhysics.CheckCapsule(spawnPos + Vector3.up * 0.6f, spawnPos + Vector3.up * 1.4f, 0.5f, Layers.Mask.World, QueryTriggerInteraction.Ignore))
                return false; // check for any rocks the player might clip into and become stuck

            return true;
        }

        public bool ResetDuelists() // reset all data for the wipe after assigning awards
        {
            if (AssignDuelists())
            {
                if (resetSeed)
                {
                    data.ResetSeed();
                }

                if (wipeDuelZones)
                {
                    data.Zones.Clear();
                    data.Spawns.Clear();
                    data.AutoGeneratedSpawns.Clear();
                }

                data.Bets.Clear();
                data.ClaimBets.Clear();
                ResetTemporaryData();
            }

            return true;
        }

        public bool AssignDuelists()
        {
            foreach (var target in covalence.Players.All) // remove player awards from previous wipe
            {
                if (permission.UserHasPermission(target.Id, duelistPerm))
                    permission.RevokeUserPermission(target.Id, duelistPerm);

                if (permission.UserHasGroup(target.Id, duelistGroup))
                    permission.RemoveUserGroup(target.Id, duelistGroup);
            }

            if (!recordStats || data.Get(Points.VictorySeed).Count == 0)
                return true; // nothing to do here, return

            if (permsToGive <= 0) // check now incase the user disabled awards later on
                return true;

            using var duelists = GetPooledList(data.Get(Points.VictorySeed)); // sort the data
            duelists.Sort((x, y) => y.Value.CompareTo(x.Value));

            int added = 0;

            for (int i = 0; i < duelists.Count; i++) // now assign it
            {
                var target = covalence.Players.FindPlayerById(duelists[i].Key);

                if (target == null || target.IsBanned || target.IsAdmin)
                    continue;

                permission.GrantUserPermission(target.Id, duelistPerm.ToLower(), this);
                permission.AddUserGroup(target.Id, duelistGroup.ToLower());

                Log("awards", msg("Awards", null, target.Name, target.Id, duelists[i].Value), true);
                Puts(msg("Granted", null, target.Name, target.Id, duelistPerm, duelistGroup));

                if (++added >= permsToGive)
                    break;
            }

            if (added > 0)
                Puts(msg("Logged", null, string.Format("{0}{1}{2}_{3}-{4}.txt", Interface.Oxide.LogDirectory, Path.DirectorySeparatorChar, Name.Replace(" ", string.Empty).ToLower(), "awards", DateTime.Now.ToString("yyyy-MM-dd"))));

            return true;
        }

        public bool IsNewman(BasePlayer player) // count the players items. exclude rocks and torchs
        {
            if (bypassNewmans)
                return true;

            int count = 0;
            for (int i = 0; i < 6; i++)
            {
                Item item = player.inventory.containerBelt.GetSlot(i);
                if (item != null && !IgnoredNakedShortnames.Contains(item.info.shortname))
                {
                    count++;
                }
            }

            for (int i = 0; i < 8; i++)
            {
                Item item = player.inventory.containerWear.GetSlot(i);
                if (item != null && !IgnoredNakedShortnames.Contains(item.info.shortname))
                {
                    count++;
                }
            }

            for (int i = 0; i < 24; i++)
            {
                Item item = player.inventory.containerMain.GetSlot(i);
                if (item != null && !IgnoredNakedShortnames.Contains(item.info.shortname))
                {
                    count++;
                }
            }

            return count <= 0;
        }

        public void LeaveEvent(BasePlayer player)
        {
            if (player == null)
                return;
            if (GetDeathmatch(player, out var match))
            {
                Reappear(player);
                match.EndMatch(match.GetTeam(player) == Team.Evil ? Team.Good : Team.Evil);
            }
            else if (IsDueling(player))
            {
                Reappear(player);
                player.inventory.Strip();
                OnDuelistLost(player, sendHome: true, ready: false);
            }
            else if (IsSpectator(player))
            {
                EndSpectate(player);
                SendHome(player);
            }

            CuiHelper.DestroyUi(player, "DuelistUI_Defeat");
        }
        
        public bool RemoveFromQueue(string targetId)
        {
            foreach (var kvp in Queued)
            {
                if (kvp.Value.ID == targetId)
                {
                    Queued.Remove(kvp.Key);
                    return true;
                }
            }

            return false;
        }

        private bool InQueue(string userid)
        {
            foreach (var data in Queued.Values)
            {
                if (data.ID == userid)
                {
                    return true;
                }
            }

            return false;
        }

        public void CheckQueue()
        {
            if (Queued.Count < 2 || !data.DuelsEnabled)
                return;

            var playerData = Queued.Values.ElementAt(0);
            var targetData = Queued.Values.ElementAt(1);
            var player = playerData.GetPlayer();
            var target = targetData.GetPlayer();

            if (player == null || !player.CanInteract() || IsTeamMember(player))
            {
                if (RemoveFromQueue(playerData.ID))
                    CheckQueue();
                return;
            }

            if (target == null || !player.CanInteract() || IsTeamMember(player))
            {
                if (RemoveFromQueue(targetData.ID))
                    CheckQueue();
                return;
            }

            if (!IsNewman(player))
            {
                if (RemoveFromQueue(player.UserIDString))
                    Message(player, "MustBeNaked");
                return;
            }

            if (!IsNewman(target))
            {
                if (RemoveFromQueue(target.UserIDString))
                    Message(target, "MustBeNaked");
                return;
            }

            SelectZone(player, target, true);
        }

        public DuelingZone GetPlayerZone(BasePlayer player, int size)
        {
            if (!playerZones.Remove(player.UserIDString, out var zone))
                return null;

            if (size > 2)
                return zone == null || zone.IsFinito || zone.IsLocked || zone.Spawns.Count < (requireTeamSize ? size * 2 : 2) ? null : zone;

            return zone == null || zone.IsFinito || zone.IsLocked || zone.Spawns.Count < requiredMinSpawns || requiredMaxSpawns > 0 && zone.Spawns.Count > requiredMaxSpawns ? null : zone;
        }

        public bool SelectZone(BasePlayer player, BasePlayer target, bool isQueued)
        {
            DuelingZone lastZone = GetPlayerZone(player, 2) ?? GetPlayerZone(target, 2);
            bool isPaymentCompleted = false;

            if (lastZone != null && lastZone.GetSelectionResult(player, target, isQueued, isPaymentRequired: true, out isPaymentCompleted) == SelectionResult.Initiate)
            {
                Initiate(player, target, false, lastZone);
                return true;
            }

            foreach (DuelingZone zone in duelingZones)
            {
                if (!IsZoneAvailable(zone, requiredMinSpawns, requiredMaxSpawns))
                    continue;

                SelectionResult result = zone.GetSelectionResult(player, target, isQueued, isPaymentRequired: !isPaymentCompleted, out _);
                if (result == SelectionResult.Full)
                    continue;

                if (result == SelectionResult.Initiate)
                    Initiate(player, target, false, zone);

                return true;
            }

            return false;
        }

        public string GetKit(BasePlayer player, BasePlayer target)
        {
            if (data.CustomKits.TryGetValue(player.UserIDString, out var p) && data.CustomKits.TryGetValue(target.UserIDString, out var t) && p.Equals(t, StringComparison.CurrentCultureIgnoreCase))
            {
                return GetVerifiedKit(p) ?? GetRandomKit();
            }

            return GetRandomKit();
        }

        public void VerifyKits()
        {
            if (lpDuelingKits.Count == 0 && hpDuelingKits.Count == 0)
            {
                return;
            }
            using var kits = GetPooledList(lpDuelingKits, hpDuelingKits);
            foreach (string kit in kits)
            {
                if (!IsKit(kit) && !customKits.ContainsKey(kit))
                {
                    lpDuelingKits.Remove(kit);
                    hpDuelingKits.Remove(kit);
                }
            }
        }

        public string GetRandomKit()
        {
            VerifyKits();

            if (lesserKitChance > 0 && lpDuelingKits.Count > 0 && Random.value < lesserKitChance)
            {
                return lpDuelingKits.GetRandom();
            }

            if (hpDuelingKits.Count > 0)
            {
                return hpDuelingKits.GetRandom();
            }

            if (customKits.Count > 0)
            {
                return customKits.ElementAt(Random.Range(0, customKits.Count)).Key;
            }

            return null;
        }

        public void Initiate(BasePlayer player, BasePlayer target, bool checkInventory, DuelingZone destZone)
        {
            try
            {
                if (player == null || target == null)
                    return;

                RemoveRequests(player);
                RemoveRequests(target);

                if (destZone == null)
                    return;

                if (checkInventory)
                {
                    if (!IsNewman(player))
                    {
                        Message(player, "MustBeNaked");
                        Message(target, "DuelMustBeNaked", player.displayName);
                        return;
                    }

                    if (!IsNewman(target))
                    {
                        Message(target, "MustBeNaked");
                        Message(player, "DuelMustBeNaked", target.displayName);
                        return;
                    }
                }

                var a = player.transform.position;
                var plyInRange = destZone.InRange(a);
                if (!plyInRange || !data.Homes.ContainsKey(player.UserIDString))
                {
                    if (IsOnConstruction(a)) a.y += 1; // prevent player from becoming stuck or dying when teleported home
                    data.Homes[player.UserIDString] = a;
                }

                var b = target.transform.position;
                var tgtInRange = destZone.InRange(b);
                if (!tgtInRange || !data.Homes.ContainsKey(target.UserIDString))
                {
                    if (IsOnConstruction(b)) b.y += 1;
                    data.Homes[target.UserIDString] = b;
                }

                var playerSpawn = destZone.Spawns.GetRandom();
                var targetSpawn = playerSpawn;
                float distSq = -1000f;

                foreach (var spawn in destZone.Spawns) // get the furthest spawn point away from the player and assign it to target
                {
                    float distanceSq = (spawn - playerSpawn).sqrMagnitude;

                    if (distanceSq > distSq)
                    {
                        distSq = distanceSq;
                        targetSpawn = spawn;
                    }
                }

                string kit = GetKit(player, target);
                data.Kits[player.UserIDString] = kit;
                data.Kits[target.UserIDString] = kit;

                Teleport(player, playerSpawn, destZone.ProtectionRadius, !plyInRange);
                Teleport(target, targetSpawn, destZone.ProtectionRadius, !tgtInRange);

                if (debugMode)
                    Puts($"{player.displayName} and {target.displayName} have entered a duel.");

                RemoveFromQueue(player.UserIDString);
                RemoveFromQueue(target.UserIDString);

                EnableUserImmunity(player, playerSpawn);
                EnableUserImmunity(target, targetSpawn);

                _duelists[player.UserIDString] = new(target);
                _duelists[target.UserIDString] = new(player);
                SubscribeHooks(true);

                Message(player, "NowDueling", target.displayName);
                Message(target, "NowDueling", player.displayName);

                if (useInvisibility)
                {
                    Disappear(player);
                    Disappear(target);
                }

                HolsterWeapon(player);
                HolsterWeapon(target);
            }
            catch (Exception ex)
            {
                SubscribeHooks(false);
                data.DuelsEnabled = false;
                SaveData();
                Puts("---\nPlugin disabled: {0} --- {1}\n---", ex.Message, ex.StackTrace);
                ResetDuelist(player.UserIDString);
                ResetDuelist(target.UserIDString);
            }
        }

        // manually check as players may not be in a clan or on a friends list

        public bool IsAllied(string playerId, string targetId)
        {
            var player = BasePlayer.Find(playerId);
            var target = BasePlayer.Find(targetId);

            return player != null && target != null && IsAllied(player, target);
        }

        private HashSet<BuildingPrivlidge> _privileges = new();
        private HashSet<CodeLock> _codes = new();
        private Coroutine _allyCo;

        private void OnEntitySpawned(BuildingPrivlidge priv) => _privileges.Add(priv);

        private void OnEntitySpawned(CodeLock codelock) => _codes.Add(codelock);

        private IEnumerator SetupAllyEntitiesCo()
        {
            int checks = 0;
            using var ents = GetPooledList(BaseNetworkable.serverEntities);
            foreach (var ent in ents)
            {
                if (++checks >= 200)
                {
                    checks = 0;
                    if (BasePlayer.activePlayerList.Count > 0)
                    {
                        yield return CoroutineEx.waitForSeconds(0.0625f);
                    }
                }
                BuildingPrivlidge priv = ent as BuildingPrivlidge;
                if (priv != null)
                {
                    _privileges.Add(priv);
                    continue;
                }
                CodeLock codelock = ent as CodeLock;
                if (codelock != null)
                {
                    _codes.Add(codelock);
                    continue;
                }
            }
            NextTick(() => _allyCo = null);
        }

        public bool IsAllied(BasePlayer player, BasePlayer target)
        {
            if (player == null || target == null || player.IsAdmin && target.IsAdmin)
                return false;

            if (IsOnSameTeam(player, target) || IsInSameClan(player, target) || IsBunked(player, target))
                return true;

            _privileges.RemoveWhere(IsNull);
            foreach (var priv in _privileges)
            {
                if (!priv.AnyAuthed() || !priv.IsAuthed(player))
                {
                    continue;
                }

                if (priv.IsAuthed(target))
                {
                    return true;
                }

                var building = priv.GetBuilding();
                if (building == null)
                {
                    continue;
                }

                var decayEntities = building.decayEntities;
                if (decayEntities.IsNullOrEmpty())
                {
                    continue;
                }

                if (decayEntities.Exists(entity => entity.OwnerID == target.userID || entity.OwnerID == player.userID))
                {
                    return true;
                }
            }

            _codes.RemoveWhere(IsNull);
            foreach (var codelock in _codes)
            {
                if (codelock.whitelistPlayers.Contains(player.userID) && codelock.whitelistPlayers.Contains(target.userID))
                {
                    return true;
                }
            }

            return false;
        }

        public bool IsOnSameTeam(BasePlayer player, BasePlayer target)
        {
            return player.currentTeam != 0 && player.Team.members.Contains(target.userID);
        }

        public bool IsInSameClan(BasePlayer player, BasePlayer target) // 1st method.
        {
            return Clans.CanCall() && Convert.ToBoolean(Clans?.Call("IsMemberOrAlly", player.UserIDString, target.UserIDString));
        }

        private bool IsBunked(BasePlayer player, BasePlayer target) // 3rd method. thanks @i_love_code for helping with this too
        {
            using var bags1 = SleepingBag.FindForPlayer(target.userID, true);
            if (bags1.Count > 0)
            {
                using var bags2 = SleepingBag.FindForPlayer(player.userID, true);
                foreach (var a in bags2)
                {
                    foreach (var b in bags1)
                    {
                        if (a.buildingID == b.buildingID)
                        {
                            return true;
                        }
                    }
                }
            }

            return false;
        }

        public void Metabolize(BasePlayer player, bool set) // we don't want the elements to harm players since the zone can spawn anywhere on the map!
        {
            if (player == null)
                return;

            if (set)
            {
                player.health = 100f;
                player.metabolism.temperature.min = 32; // immune to cold
                player.metabolism.temperature.max = 32;
                player.metabolism.temperature.value = 32;
                player.metabolism.oxygen.min = 1; // immune to drowning
                player.metabolism.oxygen.value = 1;
                player.metabolism.poison.value = 0; // if they ate raw meat
                player.metabolism.calories.value = player.metabolism.calories.max;
                player.metabolism.hydration.value = player.metabolism.hydration.max;
                player.metabolism.wetness.max = 0;
                player.metabolism.wetness.value = 0;
                player.metabolism.radiation_level.max = 0;
                player.metabolism.radiation_poison.max = 0;
            }
            else
            {
                player.metabolism.oxygen.min = 0;
                player.metabolism.oxygen.max = 1;
                player.metabolism.temperature.min = -100;
                player.metabolism.temperature.max = 100;
                player.metabolism.wetness.min = 0;
                player.metabolism.wetness.max = 1;
                player.metabolism.radiation_level.Reset();
                player.metabolism.radiation_poison.Reset();
            }

            player.metabolism.bleeding.value = 0;
            player.metabolism.SendChanges();
        }

        public bool IsKit(string kit)
        {
            return Convert.ToBoolean(Kits?.Call("isKit", kit));
        }

        public void AwardPlayer(string id, double money, int points)
        {
            if (money <= 0.0 && points <= 0)
                return;

            ulong userid = Convert.ToUInt64(id);
            if (!userid.IsSteamId())
                return;

            if (money > 0.0)
            {
                Plugin Economics = plugins.Find("Economics");
                if (Economics.CanCall())
                {
                    Economics?.Call("Deposit", userid, money);

                    var player = BasePlayer.FindByID(userid);
                    if (player != null)
                        Message(player, "EconomicsDeposit", money);
                }
            }

            if (points > 0)
            {
                Plugin ServerRewards = plugins.Find("ServerRewards");
                if (ServerRewards.CanCall())
                {
                    ServerRewards?.Call("AddPoints", userid, points);

                    var player = BasePlayer.FindByID(userid);
                    if (player != null)
                        Message(player, "ServerRewardPoints", points);
                }
            }
        }

        public void GivePlayerKit(BasePlayer player, bool isMatch)
        {
            if (player == null)
                return;

            string kit = data.Kits.Remove(player.UserIDString, out string k) ? k : string.Empty;

            player.inventory.Strip();

            if (!string.IsNullOrEmpty(kit))
            {
                if (Kits.CanCall() && IsKit(kit))
                {
                    object success = Kits.Call("GiveKit", player, kit);

                    if (success is bool && (bool)success)
                    {
                        return;
                    }
                }

                if (string.IsNullOrEmpty(kit))
                {
                    kit = data.CustomKits.ContainsKey(player.UserIDString) ? data.CustomKits[player.UserIDString] : null;
                }

                if (GiveCustomKit(player, kit, isMatch))
                {
                    return;
                }
            }

            if (Kits.CanCall())
            {
                kit = GetRandomKit();

                if (!string.IsNullOrEmpty(kit))
                {
                    object success = Kits.Call("GiveKit", player, kit);

                    if (success is bool && (bool)success)
                    {
                        return;
                    }
                }

                if (GiveCustomKit(player, kit, isMatch))
                {
                    return;
                }
            }

            // give a basic kit when no kit is provided, or the provided kit is invalid
            player.inventory.GiveItem(ItemManager.CreateByItemID(1443579727, 1, 0)); // bow
            player.inventory.GiveItem(ItemManager.CreateByItemID(-1234735557, 50, 0)); // arrows
            player.inventory.GiveItem(ItemManager.CreateByItemID(1602646136, 1, 0)); // stone spear
            player.inventory.GiveItem(ItemManager.CreateByItemID(-2072273936, 5, 0)); // bandage
            player.inventory.GiveItem(ItemManager.CreateByItemID(254522515, 3, 0)); // medkit
            player.inventory.GiveItem(ItemManager.CreateByItemID(1079279582, 4, 0)); // syringe
        }

        public bool GiveCustomKit(BasePlayer player, string kit, bool isMatch)
        {
            if (string.IsNullOrEmpty(kit) || customKits.Count == 0 || !customKits.TryGetValue(kit, out var items))
                return false;

            bool success = false;

            foreach (var dki in items)
            {
                if (isMatch && dki.shortname.Contains("hoodie"))
                {
                    continue;
                }

                ItemDefinition def = ItemManager.FindItemDefinition(dki.shortname);
                if (def == null) continue;

                ulong dkiskin = RequiresOwnership(def, dki.skin) ? 0 : dki.skin;
                Item item = ItemManager.CreateByName(dki.shortname, dki.amount, dkiskin);

                if (item == null)
                {
                    Puts("Invalid shortname {0}", dki.shortname);
                    continue;
                }

                if (item.skin == 0 && useRandomSkins)
                {
                    var skins = GetItemSkins(item.info);

                    if (skins.Count > 0)
                    {
                        ulong skin = skins.GetRandom();
                        item.skin = skin; //ItemDefinition.FindSkin(item.info.itemid, (int)skin);
                    }
                }
                
                if (dki.mods != null)
                {
                    foreach (string shortname in dki.mods)
                    {
                        Item mod = ItemManager.CreateByName(shortname, 1);

                        if (mod != null)
                            item.contents.AddItem(mod.info, 1);
                    }
                }

                var heldEntity = item.GetHeldEntity() as HeldEntity;

                if (heldEntity != null)
                {
                    if (item.skin != 0)
                        heldEntity.skinID = item.skin;

                    var weapon = heldEntity as BaseProjectile;

                    if (weapon != null)
                    {
                        if (!string.IsNullOrEmpty(dki.ammo))
                        {
                            var def2 = ItemManager.FindItemDefinition(dki.ammo);

                            if (def2 != null)
                                weapon.primaryMagazine.ammoType = def2;
                        }

                        weapon.primaryMagazine.contents = 0; // unload the old ammo
                        weapon.SendNetworkUpdateImmediate(); // update
                        weapon.primaryMagazine.contents = weapon.primaryMagazine.capacity; // load new ammo

                        heldEntity.SetHeld(false);
                    }
                }

                var container = dki.container == "belt" ? player.inventory.containerBelt : dki.container == "wear" ? player.inventory.containerWear : player.inventory.containerMain;

                item.MarkDirty();
                if (item.MoveToContainer(container, dki.slot < 0 || dki.slot > container.capacity - 1 ? -1 : dki.slot, true))
                {
                    player.UpdateActiveItem(default);
                    success = true;
                }
                else
                {
                    item.Remove(0f);
                }
            }

            return success;
        }

        private void DuelAnnouncement(bool bypass)
        {
            if (!bypass && (!data.DuelsEnabled || !useAnnouncement))
                return;

            if (BasePlayer.activePlayerList.Count < 3)
                return;

            string console = msg("DuelAnnouncement");
            string disabled = msg("Disabled");

            console = console.Replace("{duelChatCommand}", !string.IsNullOrEmpty(szDuelChatCommand) ? szDuelChatCommand : disabled);
            console = console.Replace("{ladderCommand}", !string.IsNullOrEmpty(szDuelChatCommand) ? string.Format("{0} ladder", szDuelChatCommand) : disabled);
            console = console.Replace("{queueCommand}", !string.IsNullOrEmpty(szQueueChatCommand) ? szQueueChatCommand : disabled);

            if (allowBets)
                console += msg("DuelAnnouncementBetsSuffix", null, szDuelChatCommand);

            Puts(RemoveFormatting(console));

            using var targets = GetPlayerList();
            foreach (var target in targets)
            {
                string message = msg("DuelAnnouncement", target.UserIDString);

                message = message.Replace("{duelChatCommand}", !string.IsNullOrEmpty(szDuelChatCommand) ? szDuelChatCommand : disabled);
                message = message.Replace("{ladderCommand}", !string.IsNullOrEmpty(szDuelChatCommand) ? string.Format("{0} ladder", szDuelChatCommand) : disabled);
                message = message.Replace("{queueCommand}", !string.IsNullOrEmpty(szQueueChatCommand) ? szQueueChatCommand : disabled);

                if (allowBets)
                    message += msg("DuelAnnouncementBetsSuffix", target.UserIDString, szDuelChatCommand);

                MessageB(target, $"{msg("Prefix", target.UserIDString)} <color=#C0C0C0>{message}</color>");
            }
        }

        public bool CreateBet(BasePlayer player, int betAmount, BetInfo betInfo)
        {
            if (betAmount > betInfo.max) // adjust the bet to the maximum since they clearly want to do this
                betAmount = betInfo.max;

            int amount = player.inventory.GetAmount(betInfo.itemid);

            if (amount == 0)
            {
                Message(player, "BetZero");
                return false;
            }

            if (amount < betAmount) // obviously they're just trying to see how this works. we won't adjust it here.
            {
                Message(player, "BetNotEnough");
                return false;
            }

            using var takenItems = GetPooledList<Item>();
            int takenAmount = player.inventory.Take(takenItems, betInfo.itemid, betAmount);

            if (takenAmount >= betAmount)
            {
                data.Bets.Add(player.UserIDString, new()
                {
                    itemid = betInfo.itemid,
                    amount = betAmount,
                    trigger = betInfo.trigger
                });

                using var sb = DisposableBuilder.Get();
                sb.Append(msg("BetPlaced", player.UserIDString, betInfo.trigger, betAmount));

                if (allowBetRefund)
                    sb.Append(msg("BetRefundSuffix", player.UserIDString, szDuelChatCommand));
                else if (allowBetForfeit)
                    sb.Append(msg("BetForfeitSuffix", player.UserIDString, szDuelChatCommand));

                MessageB(player, sb.ToString());
                Puts("{0} bet {1} ({2})", player.displayName, betInfo.trigger, betAmount);

                foreach (Item item in takenItems)
                    item.Remove(0.01f);

                return true;
            }

            if (takenItems.Count > 0)
            {
                foreach (Item item in takenItems)
                    player.GiveItem(item);
            }

            return false;
        }

        private bool IsBlacklistedSkin(ItemDefinition def, int num)
        {
            if (RequiresOwnership(def, (ulong)num)) return true;
            var skinId = ItemDefinition.FindSkin(def.isRedirectOf?.itemid ?? def.itemid, num);
            var dirSkin = def.isRedirectOf == null ? def.skins.FirstOrDefault(x => (ulong)x.id == skinId) : def.isRedirectOf.skins.FirstOrDefault(x => (ulong)x.id == skinId);
            var itemSkin = (dirSkin.id == 0) ? null : (dirSkin.invItem as ItemSkin);

            return itemSkin?.Redirect != null || def.isRedirectOf != null;
        }

        public List<ulong> GetItemSkins(ItemDefinition def)
        {
            if (!skinsCache.ContainsKey(def.shortname))
            {
                var skins = new List<ulong>();
                if (def.skins != null)
                {
                    foreach (var skin in def.skins)
                    {
                        if (IsBlacklistedSkin(def, skin.id))
                        {
                            continue;
                        }
                        skins.Add(Convert.ToUInt64(skin.id));
                    }
                }

                if (def.skins2 != null && useWorkshopSkins)
                {
                    foreach (var skin in def.skins2)
                    {
                        if (skin == null || IsBlacklistedSkin(def, (int)skin.WorkshopId))
                        {
                            continue;
                        }
                        if (!skins.Contains(skin.WorkshopId))
                        {
                            skins.Add(skin.WorkshopId);
                        }
                    }
                }

                skins.Remove(0uL);
                skinsCache.Add(def.shortname, skins);
            }

            return skinsCache[def.shortname];
        }

        private void RemoveRequests(BasePlayer player)
        {
            if (player != null && GetRequest(player.UserIDString, out var request))
            {
                dataRequests.Remove(request.Key);
            }
        }

        private void UpdateMatchSizeStats(string userid, int teamSize, Points stat)
        {
            if (!userid.IsSteamId()) 
                return;

            data.Add(userid, stat == Points.MatchVictory ? Points.MatchSizeVictorySeed : Points.MatchSizeLossSeed, teamSize);
            data.Add(userid, stat == Points.MatchVictory ? Points.MatchSizeVictory : Points.MatchSizeLoss, teamSize);
        }

        private void UpdateMatchStats(string userid, Points stat)
        {
            if (!userid.IsSteamId())
                return;

            switch (stat)
            {
                case Points.MatchVictory:
                    data.Add(userid, Points.MatchVictory);
                    data.Add(userid, Points.MatchVictorySeed);
                    break;
                case Points.MatchLoss:
                    data.Add(userid, Points.MatchLoss);
                    data.Add(userid, Points.MatchLossSeed);
                    break;
                case Points.MatchDeath:
                    data.Add(userid, Points.MatchDeath);
                    data.Add(userid, Points.MatchDeathSeed); 
                    break;
                case Points.MatchKill:
                    data.Add(userid, Points.MatchKill);
                    data.Add(userid, Points.MatchKillSeed);
                    break;
            }
        }

        #region Facepunch TOS Compliance

        private readonly HashSet<int> _dlcItemIds = new();
        private readonly HashSet<ulong> _ownershipIds = new();
        private bool _ownershipReady;

        private void LoadOwnership()
        {
            if (!config.BlockPaidContent)
            {
                _ownershipReady = true;
                return;
            }

            if ((Steamworks.SteamInventory.Definitions?.Length ?? 0) == 0)
            {
                timer.In(3f, LoadOwnership);
                return;
            }

            foreach (var def in ItemManager.GetItemDefinitions())
            {
                if (RequiresOwnership(def))
                {
                    _dlcItemIds.Add(def.itemid);
                }

                if (def.skins != null)
                {
                    foreach (var sk in def.skins)
                    {
                        if (sk.id != 0) _ownershipIds.Add((ulong)sk.id);
                    }
                }

                if (def.skins2 != null)
                {
                    foreach (var sk2 in def.skins2)
                    {
                        if (sk2.WorkshopId != 0) _ownershipIds.Add(sk2.WorkshopId);
                    }
                }
            }

            _ownershipReady = true;
        }

        public bool RequiresOwnership(ItemDefinition def, ulong skin)
        {
            if (!config.BlockPaidContent) return false;
            if (skin != 0uL && !_ownershipReady) return true;
            if (skin != 0uL && _ownershipIds.Contains(skin)) return true;
            if (def != null && !_ownershipReady) return RequiresOwnership(def);
            return def != null && _dlcItemIds.Contains(def.itemid);
        }

        public bool RequiresOwnership(ItemDefinition def) => def switch
        {
            null => false,
            { steamItem: { id: not 0 } } => true,
            { steamDlc: { dlcAppID: not 0 } } => true,
            { Blueprint: { NeedsSteamDLC: true } } => true,
            { Parent: { Blueprint: { NeedsSteamDLC: true } } } => true,
            { isRedirectOf: { Blueprint: { NeedsSteamDLC: true } } } => true,
            { isRedirectOf: not null } => true,
            _ => false
        };

        #endregion Facepunch TOS Compliance

        #region Networking

        private Dictionary<ulong, VanishedPlayer> VanishedPlayers = new();
        private Dictionary<ulong, VanishedWatcher> VanishedWatchers = new();

        public class VanishedPlayer
        {
            public Vector3 lastPosition;
            public BasePlayer target;
            public Transform t;
            public bool HasMoved()
            {
                if (t != null && lastPosition != t.position)
                {
                    lastPosition = t.position;
                    return true;
                }
                return false;
            }
        }

        public class VanishedWatcher
        {
            public Duelist env;
            public Timer Update;
            public ulong userid;
            public BasePlayer target;
            public bool IsConnected => target != null && target.IsConnected;
            public void SendQueueUpdate()
            {
                if (!IsConnected)
                {
                    TryUnsubscribeCanNetworkTo();
                    return;
                }
                if (env.VanishedPlayers.Count > 0 && target.CanInteract() && !target.IsSpectating())
                {
                    foreach (var vp in env.VanishedPlayers.Values)
                    {
                        if (vp.target == target || !vp.HasMoved())
                        {
                            continue;
                        }
                        target.QueueUpdate(BasePlayer.NetworkQueue.Update, vp.target);
                    }
                }
            }
            public void TryUnsubscribeCanNetworkTo()
            {
                using var watchers = GetPooledList(env.VanishedWatchers);
                foreach (var watcher in watchers)
                {
                    if (!watcher.Value.IsConnected)
                    {
                        if (watcher.Value.Update != null)
                        {
                            watcher.Value.Update.Destroy();
                        }
                        env.VanishedWatchers.Remove(watcher.Key);
                    }
                }
                if (env.VanishedWatchers.Count == 0)
                {
                    env.Unsubscribe(nameof(CanNetworkTo));
                }
            }
            public void EntityDestroyOnClient()
            {
                foreach (var vp in env.VanishedPlayers.Values)
                {
                    if (vp.target.IsValid() && vp.target != target)
                    {
                        vp.target.DestroyOnClient(target.Connection);
                    }
                }
            }
            public void SendShouldNetworkToUpdateImmediate()
            {
                foreach (var vp in env.VanishedPlayers.Values)
                {
                    if (vp.target.IsValid())
                    {
                        vp.target.SendNetworkUpdateImmediate();
                    }
                }
            }
        }

        private object CanNetworkTo(BasePlayer player, BasePlayer target)
        {
            if (player == null || target == null || player == target) // 0.1.3 fix: check if player is null
                return null;

            if (DuelTerritory(player.transform.position))
            {
                if (visibleToAdmins && target.IsAdmin && !IsParticipant(target.UserIDString))
                    return true;

                if (_duelists.TryGetValue(player.UserIDString, out var val)) // 1v1 check
                    return val.ID == target.UserIDString;

                if (spectators.Contains(player.UserIDString)) // spectator check
                    return spectators.Contains(target.UserIDString);

                if (InDeathmatch(player)) // tdm check
                    return InDeathmatch(target);
            }

            return null;
        }

        //private object CanNetworkTo(HeldEntity heldEntity, BasePlayer target)
        //{
        //    if (heldEntity == null)
        //        return null;
        //    BasePlayer player = heldEntity.GetOwnerPlayer();
        //    if (player == null)
        //        return null;
        //    return CanNetworkTo(player, target); // 0.1.3 fix: check if player is null
        //}

        public void Disappear(BasePlayer player)
        {
            if (VanishedPlayers.ContainsKey(player.userID))
                return;
            VanishedPlayers[player.userID] = new()
            {
                target = player,
                t = player.transform
            };
            //player.syncPosition = false;
            player.limitNetworking = true;
            VanishedWatcher vw = null;
            VanishedWatchers[player.userID] = vw = new()
            {
                env = this,
                target = player,
                userid = player.userID,
                Update = timer.Every(0.1f, () => vw.SendQueueUpdate())
            };
            if (VanishedWatchers.Count == 1)
            {
                Subscribe(nameof(CanNetworkTo));
            }
            vw.SendShouldNetworkToUpdateImmediate();
            HolsterWeapon(player);
        }

        public void Reappear(BasePlayer player)
        {
            if (VanishedWatchers.Remove(player.userID, out var vw))
            {
                vw.Update.Destroy();
                vw.EntityDestroyOnClient();
                vw.TryUnsubscribeCanNetworkTo();
            }
            if (VanishedPlayers.Remove(player.userID))
            {
                //player.syncPosition = true;
                player.limitNetworking = false;
            }
        }

        //private void InitializeNetworking()
        //{
        //    using var targets = GetPlayerList();
        //    foreach (var target in targets)
        //    {
        //        if (target.limitNetworking)
        //        {
        //            OnVanishDisappear(target);
        //        }
        //    }
        //}

        //private void EntityDestroyOnClient()
        //{
        //    foreach (var vw in VanishedWatchers.Values)
        //    {
        //        if (vw.IsConnected)
        //        {
        //            vw.EntityDestroyOnClient();
        //        }
        //    }
        //}

        //public void EntityDestroyOnClient(BasePlayer player)
        //{
        //    foreach (var vp in VanishedPlayers.Values)
        //    {
        //        if (vp.target.IsValid() && vp.target != player)
        //        {
        //            vp.target.DestroyOnClient(player.Connection);
        //        }
        //    }
        //}

        //private void OnVanishDisappear(BasePlayer player)
        //{
        //    VanishedPlayers[player.userID] = new()
        //    {
        //        target = player,
        //        t = player.transform
        //    };
        //}

        //private void OnVanishReappear(BasePlayer player)
        //{
        //    VanishedPlayers.Remove(player.userID);
        //}

        #endregion Networking

        #region SpawnPoints

        public void SendSpawnHelp(BasePlayer player)
        {
            Message(player, "SpawnCount", data.Spawns.Count);
            Message(player, "SpawnAdd", szDuelChatCommand);
            Message(player, "SpawnHere", szDuelChatCommand);
            Message(player, "SpawnRemove", szDuelChatCommand, spRemoveOneMaxDistance);
            Message(player, "SpawnRemoveAll", szDuelChatCommand, spRemoveAllMaxDistance);
            Message(player, "SpawnWipe", szDuelChatCommand);
        }

        public void AddSpawnPoint(BasePlayer player, bool useHit)
        {
            var spawn = player.transform.position;

            if (useHit)
            {
                if (!Physics.Raycast(player.eyes.HeadRay(), out var hit, Mathf.Infinity, wallMask))
                {
                    Message(player, "FailedRaycast");
                    return;
                }

                spawn = hit.point;
            }

            spawn = spawn.SnapTo(0.001f);
            if (data.Spawns.Contains(spawn))
            {
                Message(player, "SpawnExists");
                return;
            }

            data.Spawns.Add(spawn);
            player.SendConsoleCommand("ddraw.text", spDrawTime, Color.green, spawn, "+S");
            Message(player, "SpawnAdded", FormatPosition(spawn));
            ClearSpawns(spawn);
        }

        public void RemoveSpawnPoint(BasePlayer player)
        {
            float radius = spRemoveOneMaxDistance;
            var spawn = Vector3.zero;
            float dist = radius;

            foreach (var s in data.Spawns)
            {
                float distance = Vector3.Distance(player.transform.position, s);

                if (distance < dist)
                {
                    dist = distance;
                    spawn = s;
                }
            }

            if (spawn != Vector3.zero)
            {
                data.Spawns.Remove(spawn);
                player.SendConsoleCommand("ddraw.text", spDrawTime, Color.red, spawn, "-S");
                Message(player, "SpawnRemoved", 1);
                ClearSpawns(spawn);
            }
            else Message(player, "SpawnNoneFound", radius);
        }

        public void RemoveSpawnPoints(BasePlayer player)
        {
            int count = 0;
            using var spawns = GetPooledList(data.Spawns);
            foreach (var spawn in spawns)
            {
                if (Vector3.Distance(player.transform.position, spawn) <= spRemoveAllMaxDistance)
                {
                    count++;
                    data.Spawns.Remove(spawn);
                    ClearSpawns(spawn);
                    player.SendConsoleCommand("ddraw.text", spDrawTime, Color.red, spawn, "-S");
                }
            }

            if (count == 0)
            {
                Message(player, "SpawnNoneFound", spRemoveAllMaxDistance);
            }
            else Message(player, "SpawnRemoved", count);
        }

        public void ClearSpawns(Vector3 spawn)
        {
            foreach (var zone in duelingZones)
            {
                if (zone.SqrDistance(spawn) <= zone.SqrProtectionRadius)
                {
                    zone.ClearSpawns();
                }
            }
        }

        public void WipeSpawnPoints(BasePlayer player)
        {
            if (data.Spawns.Count == 0)
            {
                Message(player, "SpawnNoneExist");
                return;
            }

            foreach (var spawn in data.Spawns)
                player.SendConsoleCommand("ddraw.text", 30f, Color.red, spawn, "-S");

            int amount = data.Spawns.Count;
            data.Spawns.Clear();
            Message(player, "SpawnWiped", amount);
        }

        public List<Vector3> GetSpawnPoints(DuelingZone zone)
        {
            var spawns = new List<Vector3>();
            foreach (var spawn in data.Spawns)
            {
                if (zone.SqrDistance(spawn) <= zone.SqrProtectionRadius)
                    spawns.Add(spawn);
            }
            return spawns;
        }

        public string FormatPosition(Vector3 position)
        {
            return $"{position.x:N2} {position.y:N2} {position.z:N2}";
        }

        #endregion SpawnPoints

        #region UI Creation 

        private readonly List<string> createUI = new();
        private readonly List<string> duelistUI = new();
        private readonly List<string> kitsUI = new();
        private readonly List<string> matchesUI = new();

        [ConsoleCommand("UI_DuelistCommand")]
        private void ccmdDuelistUI(ConsoleSystem.Arg arg)
        {
            var player = arg.Player();
            if (IsNotConnected(player) || !arg.HasArgs())
                return;

            var user = player.IPlayer;
            switch (arg.Args[0].ToLower())
            {
                case "accept":
                    {
                        if (HasPendingRequest(player.UserIDString))
                        {
                            CommandDuelist(user, szDuelChatCommand, new[] { "accept" });
                            break;
                        }
                        if (HasRequestSender(player))
                        {
                            CommandDeathmatch(user, szMatchChatCommand, new[] { "accept" });
                            break;
                        }

                        Message(player, "NoPendingRequests2");
                        break;
                    }
                case "decline":
                    {
                        if (HasRequest(player.UserIDString))
                        {
                            CommandDuelist(user, szDuelChatCommand, new[] { "decline" });
                            break;
                        }

                        var deathmatch = tdmMatches.FirstOrDefault(x => x.GetTeam(player) != Team.None);

                        if (deathmatch != null || HasRequestTarget(player) || HasRequestSender(player))
                        {
                            CommandDeathmatch(user, szMatchChatCommand, new[] { "decline" });
                            break;
                        }

                        Message(player, "NoPendingRequests");
                        break;
                    }
                case "closeui":
                    {
                        DestroyUI(player);
                        return;
                    }
                case "kits":
                    {
                        ToggleKitUI(player);
                        break;
                    }
                case "public":
                    {
                        CommandDeathmatch(user, szMatchChatCommand, new[] { "public" });
                        break;
                    }
                case "requeue":
                    {
                        if (InEvent(player))
                            return;

                        if (sendHomeRequeue)
                        {
                            CuiHelper.DestroyUi(player, "DuelistUI_Defeat");
                            SendHome(player);
                        }
                        else CreateDefeatUI(player);
                        CommandQueue(user, szQueueChatCommand, new string[0]);
                        return;
                    }
                case "queue":
                    {
                        if (InEvent(player))
                            break;

                        CommandQueue(user, szQueueChatCommand, new string[0]);
                        break;
                    }
                case "respawn":
                    {
                        LeaveEvent(player);

                        return;
                    }
                case "ready":
                case "readyon":
                case "readyoff":
                    {
                        ReadyUp(player);

                        if (DuelTerritory(player.transform.position))
                        {
                            CreateDefeatUI(player);
                            return;
                        }

                        break;
                    }
                case "tdm":
                    {
                        ToggleMatchUI(player);
                        break;
                    }
                case "kit":
                    {
                        if (arg.Args.Length != 2)
                            return;

                        if (GetDeathmatch(player, out var match) && match.IsHost(player))
                        {
                            if (!match.IsStarted)
                                match.Kit = GetVerifiedKit(arg.Args[1]); // UI

                            break;
                        }

                        if (data.CustomKits.ContainsKey(player.UserIDString) && data.CustomKits[player.UserIDString] == arg.Args[1])
                        {
                            data.CustomKits.Remove(player.UserIDString);
                            Message(player, "ResetKit");
                            break;
                        }

                        string kit = GetVerifiedKit(arg.Args[1].Replace("||", " ")); // UI

                        if (string.IsNullOrEmpty(kit))
                            break;

                        data.CustomKits[player.UserIDString] = kit;
                        Message(player, "KitSet", kit);
                        break;
                    }
                case "joinmatch":
                    {
                        if (arg.Args.Length != 2)
                            return;

                        if (IsDueling(player))
                            break;

                        if (GetDeathmatch(player, out var match))
                        {
                            if (match.IsStarted)
                                break;

                            match.RemoveMatchPlayer(player);
                        }

                        var newMatch = tdmMatches.FirstOrDefault(x => x.Id == arg.Args[1] && x.IsPublic);

                        if (newMatch == null || newMatch.IsFull() || newMatch.IsStarted || newMatch.IsOver)
                        {
                            Message(player, "MatchNoLongerValid");
                            break;
                        }

                        if (newMatch.GetTeam(player) != Team.None)
                            break;

                        newMatch.AddMatchPlayer(player, !newMatch.IsFull(Team.Good) ? Team.Good : Team.Evil);

                        if (matchesUI.Contains(player.UserIDString))
                        {
                            CuiHelper.DestroyUi(player, "DuelistUI_Matches");
                            matchesUI.Remove(player.UserIDString);
                        }

                        break;
                    }
                case "size":
                    {
                        if (arg.Args.Length != 2 || !arg.Args[1].All(char.IsDigit))
                            break;

                        CommandDeathmatch(user, szMatchChatCommand, new[] { "size", arg.Args[1] });
                        break;
                    }
                case "any":
                    {
                        CommandDeathmatch(user, szMatchChatCommand, new[] { "any" });
                        break;
                    }
            }

            RefreshUI(player);
        }

        public void DestroyAllUI()
        {
            using var targets = GetPlayerList();
            foreach (var target in targets)
            {
                DestroyUI(target);
            }
        }

        public bool DestroyUI(BasePlayer player)
        {
            CuiHelper.DestroyUi(player, "DuelistUI_Options");
            CuiHelper.DestroyUi(player, "DuelistUI_Kits");
            CuiHelper.DestroyUi(player, "DuelistUI_Matches");
            CuiHelper.DestroyUi(player, "DuelistUI_Announcement");
            CuiHelper.DestroyUi(player, "DuelistUI_Defeat");
            CuiHelper.DestroyUi(player, "DuelistUI_Countdown");

            if (readyUiList.Remove(player.UserIDString))
            {
                CuiHelper.DestroyUi(player, "DuelistUI_Ready");
            }

            return duelistUI.Remove(player.UserIDString);
        }

        public void ccmdDUI(ConsoleSystem.Arg arg)
        {
            var player = arg.Player();

            if (IsNull(player))
                return;

            if (arg.HasArgs(1))
            {
                switch (arg.Args[0].ToLower())
                {
                    case "on":
                        {
                            cmdDUI(player, szUIChatCommand, Array.Empty<string>());
                            return;
                        }
                    case "off":
                        {
                            DestroyUI(player);
                            return;
                        }
                }
            }

            if (duelistUI.Contains(player.UserIDString))
                DestroyUI(player);
            else
                cmdDUI(player, szUIChatCommand, Array.Empty<string>());
        }

        public void cmdDUI(BasePlayer player, string command, string[] args)
        {
            DestroyUI(player);
            var buttons = new List<string>
            {
                "UI_Accept",
                "UI_Decline",
                "UI_Kits",
                "UI_Public",
                "UI_Queue",
                "UI_TDM",
                "UI_Any"
            };

            if (!autoReady)
            {
                buttons.Add(data.AutoReady.Contains(player.UserIDString) ? "UI_ReadyOn" : "UI_ReadyOff");
            }

            var element = UI.CreateElementContainer("DuelistUI_Options", "0 0 0 0.5", "0.915 0.148", "0.981 0.441", guiUseCursor);

            if (guiUseCloseButton)
                UI.CreateButton(ref element, "DuelistUI_Options", "0.29 0.49 0.69 0.5", "X", 14, "0.7 0.9", "0.961 0.98", "UI_DuelistCommand closeui");

            for (int number = 0; number < buttons.Count; number++)
            {
                var pos = UI.CalcButtonPos(number + 1, 2.075f);
                string uicommand = buttons[number].Replace("UI_", string.Empty).ToLower();
                string text = msg(buttons[number], player.UserIDString);
                UI.CreateButton(ref element, "DuelistUI_Options", "0.29 0.49 0.69 0.5", text, 14, $"{pos[0]} {pos[1]}", $"{pos[2]} {pos[3]}", $"UI_DuelistCommand {uicommand}");
            }

            if (!duelistUI.Contains(player.UserIDString))
                duelistUI.Add(player.UserIDString);

            CuiHelper.AddUi(player, element);
        }

        public void RefreshUI(BasePlayer player)
        {
            cmdDUI(player, szUIChatCommand, Array.Empty<string>());

            if (kitsUI.Contains(player.UserIDString))
            {
                kitsUI.Remove(player.UserIDString);
                ToggleKitUI(player);
            }
            if (matchesUI.Contains(player.UserIDString))
            {
                matchesUI.Remove(player.UserIDString);
                ToggleMatchUI(player);
            }
        }

        public void ToggleMatchUI(BasePlayer player)
        {
            if (matchesUI.Contains(player.UserIDString))
            {
                CuiHelper.DestroyUi(player, "DuelistUI_Matches");
                matchesUI.Remove(player.UserIDString);
                return;
            }

            if (kitsUI.Contains(player.UserIDString))
            {
                CuiHelper.DestroyUi(player, "DuelistUI_Kits");
                kitsUI.Remove(player.UserIDString);
            }

            var element = UI.CreateElementContainer("DuelistUI_Matches", "0 0 0 0.5", "0.669 0.148", "0.903 0.541");
            using var matches = GetPooledList(tdmMatches.Where(x => x.IsPublic && !x.IsStarted && !x.IsFull()));

            for (int number = 0; number < matches.Count; number++)
            {
                var pos = UI.CalcButtonPos(number);
                UI.CreateButton(ref element, "DuelistUI_Matches", "0.29 0.49 0.69 0.5", matches[number].Versus, 12, $"{pos[0]} {pos[1]}", $"{pos[2]} {pos[3]}", $"UI_DuelistCommand joinmatch {matches[number].Id}");
            }

            GetDeathmatch(player, out var match);
            string teamSize = msg("UI_TeamSize", player.UserIDString);

            for (int size = Math.Max(2, minDeathmatchSize); size < maxDeathmatchSize + 1; size++)
            {
                var pos = UI.CalcButtonPos(size + matches.Count);
                string color = match != null && match.TeamSize == size || size == minDeathmatchSize ? "0.69 0.49 0.29 0.5" : "0.29 0.49 0.69 0.5";
                UI.CreateButton(ref element, "DuelistUI_Matches", color, teamSize + size, 12, $"{pos[0]} {pos[1]}", $"{pos[2]} {pos[3]}", $"UI_DuelistCommand size {size}");
            }

            if (matches.Count == 0)
                UI.CreateLabel(ref element, "DuelistUI_Matches", "1 1 1 1", msg("NoMatchesExistYet", player.UserIDString), 14, "0.047 0.73", "1 0.89");

            CuiHelper.AddUi(player, element);
            matchesUI.Add(player.UserIDString);
        }

        public void ToggleKitUI(BasePlayer player)
        {
            if (kitsUI.Contains(player.UserIDString))
            {
                CuiHelper.DestroyUi(player, "DuelistUI_Kits");
                kitsUI.Remove(player.UserIDString);
                return;
            }

            if (matchesUI.Contains(player.UserIDString))
            {
                CuiHelper.DestroyUi(player, "DuelistUI_Matches");
                matchesUI.Remove(player.UserIDString);
            }

            var element = UI.CreateElementContainer("DuelistUI_Kits", "0 0 0 0.5", "0.669 0.148", "0.903 0.541");
            var kits = VerifiedKits;
            string kit = data.CustomKits.ContainsKey(player.UserIDString) ? data.CustomKits[player.UserIDString] : null;

            for (int number = 0; number < kits.Count; number++)
            {
                var pos = UI.CalcButtonPos(number);
                UI.CreateButton(ref element, "DuelistUI_Kits", kits[number] == kit ? "0.69 0.49 0.29 0.5" : "0.29 0.49 0.69 0.5", kits[number], 12, $"{pos[0]} {pos[1]}", $"{pos[2]} {pos[3]}", $"UI_DuelistCommand kit {kits[number].Replace(" ", "||")}");
            }

            CuiHelper.AddUi(player, element);
            kitsUI.Add(player.UserIDString);
        }

        public void CreateAnnouncementUI(BasePlayer player, string text)
        {
            if (guiAnnounceUITime <= 0f || IsNotConnected(player) || string.IsNullOrEmpty(text))
                return;

            var element = UI.CreateElementContainer("DuelistUI_Announcement", "0 0 0 0.5", "-0.027 0.92", "1.026 0.9643", false, "Hud");

            UI.CreateLabel(ref element, "DuelistUI_Announcement", string.Empty, text, 18, "0 0", "1 1");
            CuiHelper.DestroyUi(player, "DuelistUI_Announcement");
            CuiHelper.AddUi(player, element);

            timer.Once(guiAnnounceUITime, () => CuiHelper.DestroyUi(player, "DuelistUI_Announcement"));
        }

        public void CreateCountdownUI(BasePlayer player, float countdown)
        {
            var element = UI.CreateElementContainer("DuelistUI_Countdown", "0 0 0 0.5", "0.484 0.92", "0.527 0.9643", false, "Hud");

            UI.CreateLabel(ref element, "DuelistUI_Countdown", "1 0.1 0.1 1", countdown.ToString(), 20, "0 0", "1 1");
            CuiHelper.DestroyUi(player, "DuelistUI_Countdown");
            CuiHelper.AddUi(player, element);
        }

        public void ToggleReadyUI(BasePlayer player)
        {
            if (autoReady || IsNotConnected(player))
                return;

            if (readyUiList.Contains(player.UserIDString))
            {
                CuiHelper.DestroyUi(player, "DuelistUI_Ready");
                readyUiList.Remove(player.UserIDString);
                return;
            }

            var element = UI.CreateElementContainer("DuelistUI_Ready", "0 0 0 0.5", "0.475 0.158", "0.573 0.21");
            UI.CreateButton(ref element, "DuelistUI_Ready", "0.29 0.49 0.69 0.5", msg(autoReady || data.AutoReady.Contains(player.UserIDString) ? "UI_ReadyOn" : "UI_ReadyOff", player.UserIDString), 18, "0.016 0.081", "0.984 0.919", "UI_DuelistCommand ready");
            CuiHelper.AddUi(player, element);
            readyUiList.Add(player.UserIDString);
        }

        public void CreateDefeatUI(BasePlayer player)
        {
            if (IsNotConnected(player))
                return;

            var element = UI.CreateElementContainer("DuelistUI_Defeat", "0 0 0 0.5", "0.436 0.133", "0.534 0.307", guiUseCursor);

            UI.CreateButton(ref element, "DuelistUI_Defeat", "0.29 0.49 0.69 0.5", msg("UI_Respawn", player.UserIDString), 18, "0.016 0.679", "0.984 0.976", "UI_DuelistCommand respawn");
            UI.CreateButton(ref element, "DuelistUI_Defeat", "0.29 0.49 0.69 0.5", msg("UI_Requeue", player.UserIDString), 18, "0.016 0.357", "0.984 0.655", "UI_DuelistCommand requeue");
            if (!autoReady) UI.CreateButton(ref element, "DuelistUI_Defeat", "0.29 0.49 0.69 0.5", msg(autoReady || data.AutoReady.Contains(player.UserIDString) ? "UI_ReadyOn" : "UI_ReadyOff", player.UserIDString), 18, "0.016 0.024", "0.984 0.333", "UI_DuelistCommand ready");
            CuiHelper.DestroyUi(player, "DuelistUI_Defeat");
            CuiHelper.AddUi(player, element);

            if (readyUiList.Contains(player.UserIDString))
            {
                CuiHelper.DestroyUi(player, "DuelistUI_Ready");
                readyUiList.Remove(player.UserIDString);
            }
        }

        private void UpdateMatchUI()
        {
            if (!matchUpdateRequired)
                return;

            matchUpdateRequired = false;

            using var matches = GetPooledList(matchesUI);
            foreach (string userId in matches)
            {
                matchesUI.Remove(userId);
                var player = BasePlayer.Find(userId);

                if (player != null && player.IsConnected)
                {
                    CuiHelper.DestroyUi(player, "DuelistUI_Matches");
                    ToggleMatchUI(player);
                }
            }
        }

        public class UI // Credit: Absolut
        {
            public static CuiElementContainer CreateElementContainer(string panelName, string color, string aMin, string aMax, bool cursor = false, string parent = "Overlay")
            {
                var NewElement = new CuiElementContainer
                {
                    {
                        new CuiPanel
                        {
                            Image =
                            {
                                Color = color
                            },
                            RectTransform =
                            {
                                AnchorMin = aMin,
                                AnchorMax = aMax
                            },
                            CursorEnabled = cursor
                        },
                        new CuiElement().Parent = parent,
                        panelName
                    }
                };
                return NewElement;
            }

            public static void CreateLabel(ref CuiElementContainer container, string panel, string color, string text, int size, string aMin, string aMax, TextAnchor align = TextAnchor.MiddleCenter)
            {
                container.Add(new CuiLabel
                {
                    Text =
                    {
                        Color = color,
                        FontSize = size,
                        Align = align,
                        FadeIn = 1.0f,
                        Text = text
                    },
                    RectTransform =
                    {
                        AnchorMin = aMin,
                        AnchorMax = aMax
                    }
                },
                panel);
            }

            public static void CreateButton(ref CuiElementContainer container, string panel, string color, string text, int size, string aMin, string aMax, string command, TextAnchor align = TextAnchor.MiddleCenter, string labelColor = "")
            {
                container.Add(new CuiButton
                {
                    Button =
                        {
                            Color = color,
                            Command = command,
                            FadeIn = 1.0f
                        },
                    RectTransform =
                        {
                            AnchorMin = aMin,
                            AnchorMax = aMax
                        },
                    Text =
                        {
                            Text = text,
                            FontSize = size,
                            Align = align,
                            Color = labelColor
                        }
                },
                    panel);
            }

            public static float[] CalcButtonPos(int number, float dMinOffset = 1f)
            {
                Vector2 position = new(0.03f, 0.889f);
                Vector2 dimensions = new(0.45f * dMinOffset, 0.1f);
                float offsetY = 0;
                float offsetX = 0;
                if (number >= 0 && number < 9)
                {
                    offsetY = (-0.01f - dimensions.y) * number;
                }
                else if (number > 8 && number < 19)
                {
                    offsetY = (-0.01f - dimensions.y) * (number - 9);
                    offsetX = (0.04f + dimensions.x) * 1;
                }
                else if (number > 18 && number < 29)
                {
                    offsetY = (-0.01f - dimensions.y) * (number - 19);
                    offsetX = (0.08f + dimensions.x) * 1;
                }
                Vector2 offset = new(offsetX, offsetY);
                Vector2 posMin = position + offset;
                Vector2 posMax = posMin + dimensions;
                return new[] { posMin.x, posMin.y, posMax.x, posMax.y };
            }
        }

        #endregion UI Creation

        #region Config

        private const string duelistPerm = "duelist.dd";
        private const string duelistGroup = "duelist";
        private List<string> _hpDuelingKits = new();
        private List<string> _lpDuelingKits = new();
        private List<string> hpDuelingKits = new();
        private List<string> lpDuelingKits = new();
        private Dictionary<string, List<DuelKitItem>> customKits => config.CustomKits.Kits;

        private string szMatchChatCommand => config.Deathmatch.szMatchChatCommand;
        private string szDuelChatCommand => config.Settings.szDuelChatCommand;
        private string szQueueChatCommand => config.Settings.szQueueChatCommand;
        private int deathTime => config.Settings.deathTime;
        private int immunityTime => config.Settings.immunityTime;
        private int zoneCounter => config.Zones.zoneCounter;
        private List<BetInfo> cfg_duelingBets => config.Betting.Bets;
        private List<BetInfo> duelingBets = new();
        private bool recordStats => config.Ranked.recordStats;
        private int permsToGive => config.Ranked.permsToGive;
        private float maxIncline => config.Zones.maxIncline;
        private bool allowBetForfeit => config.Betting.allowBetForfeit;
        private bool allowBetRefund => config.Betting.allowBetRefund;
        private bool allowBets => config.Betting.allowBets;
        private bool putToSleep => config.Animals.putToSleep;
        private bool blockSpawning => config.Settings.blockSpawning;
        private bool killNpc => config.Animals.killNpc;
        private float announceTime => config.Settings.announceTime;
        private bool removePlayers => config.Settings.removePlayers;
        private bool useAnnouncement => config.Settings.useAnnouncement;
        private bool autoSetup => config.Settings.autoSetup;
        private bool broadcastDefeat => config.Settings.broadcastDefeat;
        private double economicsMoney => config.Rewards.economicsMoney;
        private CustomCostOption requiredDuelPaymentOption => config.Rewards.requiredDuelPaymentOption;
        private int serverRewardsPoints => config.Rewards.serverRewardsPoints;
        private float damageScaleAmount => config.Settings.damageScaleAmount;
        private int zoneAmount => config.Zones.zoneAmount;
        private int playersPerZone => config.Zones.playersPerZone;
        private bool visibleToAdmins => config.Zones.visibleToAdmins;
        private float spDrawTime => config.Spawns.spDrawTime;
        private float spRemoveOneMaxDistance => config.Spawns.spRemoveOneMaxDistance;
        private float spRemoveAllMaxDistance => config.Spawns.spRemoveAllMaxDistance;
        private bool spAutoRemove => config.Spawns.spAutoRemove;
        private bool avoidWaterSpawns => config.Zones.avoidWaterSpawns;
        private bool useInvisibility => config.Settings.useInvisibility;
        private int extraWallStacks => config.Zones.extraWallStacks;
        private bool useZoneWalls => config.Zones.useZoneWalls;
        private bool zoneUseWoodenWalls => config.Zones.zoneUseWoodenWalls;
        private float buildingBlockExtensionRadius => config.Settings.buildingBlockExtensionRadius;
        private bool autoAllowAll => config.Settings.autoAllowAll;
        private bool useRandomSkins => config.Settings.useRandomSkins;
        private float playerHealth => config.Settings.playerHealth;
        private bool dmFF => config.Deathmatch.dmFF;
        private bool jitteredSpawns => config.Deathmatch.jitteredSpawns;
        private int minDeathmatchSize => config.Deathmatch.minDeathmatchSize;
        private int maxDeathmatchSize => config.Deathmatch.maxDeathmatchSize;
        private bool autoEnable => config.Settings.autoEnable;
        private ulong teamGoodShirt => config.Deathmatch.teamGoodShirt;
        private ulong teamEvilShirt => config.Deathmatch.teamEvilShirt;
        private string teamShirt => config.Deathmatch.teamShirt;
        private double teamEconomicsMoney => config.Deathmatch.teamEconomicsMoney;
        private int teamServerRewardsPoints => config.Deathmatch.teamServerRewardsPoints;
        private float lesserKitChance => config.Settings.lesserKitChance;
        private bool tdmEnabled => config.Deathmatch.tdmEnabled;
        private bool useLeastAmount => config.Zones.useLeastAmount;
        private bool tdmServerDeaths => config.Deathmatch.tdmServerDeaths;
        private bool tdmMatchDeaths => config.Deathmatch.tdmMatchDeaths;
        private List<string> whitelistCommands = new();
        private bool useWhitelistCommands => config.Settings.useWhitelistCommands;
        private List<string> blacklistCommands => config.Settings.blacklistCommands;
        private bool useBlacklistCommands => config.Settings.useBlacklistCommands;
        private bool bypassNewmans => config.Settings.bypassNewmans;
        private List<string> IgnoredNakedShortnames => config.Settings.ignoredNakedItems;
        private List<DuelKitItem> respawnLoot => config.Respawn.respawnLoot;
        private bool respawnDeadDisconnect => config.Settings.respawnDeadDisconnect;
        private bool sendDeadHome => config.Advanced.sendDeadHome;
        private bool resetSeed => config.Settings.resetSeed;
        private bool noStability => config.Settings.noStability;
        private bool noMovement => config.Settings.noMovement;
        private bool requireTeamSize => config.Advanced.requireTeamSize;
        private int requiredMinSpawns => config.Advanced.requiredMinSpawns;
        private int requiredMaxSpawns => config.Advanced.requiredMaxSpawns;
        private bool guiAutoEnable => config.UserInterface.guiAutoEnable;
        private bool guiUseCursor => config.UserInterface.guiUseCursor;
        private string szUIChatCommand => config.UserInterface.szUIChatCommand;
        private bool useWorkshopSkins => config.CustomKits.useWorkshopSkins;
        private bool respawnWalls => config.Settings.respawnWalls;
        private bool allowPlayerDeaths => config.Advanced.allowPlayerDeaths;
        private bool morphBarricadesStoneWalls => config.Deployables.morphBarricadesStoneWalls;
        private bool morphBarricadesWoodenWalls => config.Deployables.morphBarricadesWoodenWalls;
        private bool guiUseCloseButton => config.UserInterface.guiUseCloseButton;
        private string autoKitName => config.Respawn.autoKitName;
        private float guiAnnounceUITime => config.UserInterface.guiAnnounceUITime;
        private bool sendDefeatedHome => config.Advanced.sendDefeatedHome;
        private bool sendHomeRequeue => config.UserInterface.sendHomeRequeue;
        private bool sendHomeSpectatorWhenRematchTimesOut => config.Spectators.sendHomeSpectatorWhenRematchTimesOut;
        private bool autoFlames => config.Devices.autoFlames;
        private bool autoOvens => config.Devices.autoOvens;
        private bool autoTurrets => config.Devices.autoTurrets;
        private int sphereAmount => config.Settings.sphereAmount;
        private bool wipeDuelZones => config.Settings.wipeDuelZones;
        private bool setPlayerTime => config.Settings.setPlayerTime;
        private ulong chatSteamID => config.Settings.chatSteamID;
        private float zoneRadius => config.Zones.zoneRadius;
        private bool autoReady => config.Settings.autoReady;

        private static List<string> BlacklistedCommands
        {
            get
            {
                return new()
                {
                    "/tp",
                    "/remove",
                    "/bank",
                    "/shop",
                    "/event",
                    "/rw",
                    "/home",
                    "/trade"
                };
            }
        }

        private static List<string> WhitelistedCommands
        {
            get
            {
                return new()
                {
                    "/report",
                    "/pm",
                    "/r",
                    "/help"
                };
            }
        }

        private static List<object> DefaultBets
        {
            get
            {
                return new List<object>
                {
                    new BetInfo(null, "stone", 50000, -2099697608),
                    new BetInfo(null, "sulfur", 50000, -1581843485),
                    new BetInfo(null, "fragment", 50000, 69511070),
                    new BetInfo(null, "charcoal", 50000, -1938052175),
                    new BetInfo(null, "gp", 25000, -265876753),
                    new BetInfo(null, "hqm", 1000, 317398316),
                    new BetInfo(null, "c4", 10, 1248356124),
                    new BetInfo(null, "rocket", 6, -742865266),
                };
            }
        }

        private static List<string> DefaultLesserKits
        {
            get
            {
                return new List<string>
                {
                    "kit_4",
                    "kit_5",
                    "kit_6"
                };
            }
        }

        private static List<string> DefaultKits
        {
            get
            {
                return new List<string>
                {
                    "kit_1",
                    "kit_2",
                    "kit_3"
                };
            }
        }

        protected override void LoadDefaultMessages() // holy shit this took forever.
        {
            lang.RegisterMessages(new()
            {
                ["Awards"] = "{0} ({1}) duels won {2}",
                ["Granted"] = "Granted {0} ({1}) permission {2} for group {3}",
                ["Logged"] = "Duelists have been logged to: {0}",
                ["Indestructible"] = "This object belongs to the server and is indestructible!",
                ["Building is blocked!"] = "<color=#FF0000>Building is blocked inside of dueling zones!</color>",
                ["TopAll"] = "[ <color=#ffff00>Top Duelists Of All Time ({0})</color> ]:",
                ["Top"] = "[ <color=#ffff00>Top Duelists ({0})</color> ]:",
                ["NoLongerQueued"] = "You are no longer in queue for a duel.",
                ["InQueueSuccess"] = "You are now in queue for a duel. You will teleport instantly when a match is available.",
                ["MustBeNaked"] = "<color=#FF0000>You must be naked before you can duel.</color>",
                ["AlreadyInADuel"] = "You cannot queue for a duel while already in a duel!",
                ["MustAllowDuels"] = "You must allow duels first! Type: <color=#FFA500>/{0} allow</color>",
                ["DuelsDisabled"] = "Duels are disabled.",
                ["NoZoneExists"] = "No dueling zone exists.",
                ["Banned"] = "You are banned from duels.",
                ["FoundZone"] = "Took {0} tries ({1}ms) to get a dueling zone.",
                ["ImmunityFaded"] = "Your immunity has faded.",
                ["NotifyBetWon"] = "You have won your bet! To claim type <color=#FFA500>/{0} claim</color>.",
                ["ConsoleBetWon"] = "{0} ({1}) won his bet against {2} ({3})!",
                ["DuelDeathMessage"] = "<color=#C0C0C0><color=#00FF00>{0}</color> (<color=#00FF00>W</color>: <color=#FFA500>{1}</color> / <color=#FF0000>L</color>: <color=#FFA500>{2}</color>) <color=#000000>→</color> <color=#00FF00>{3}</color> (<color=#00FF00>W</color>: <color=#FFA500>{4}</color> / <color=#FF0000>L</color>: <color=#FFA500>{5}</color>): 1v1 (<color=#00FF00>{6}</color> <color=#FFA500>HP</color>){7}</color>",
                ["BetWon"] = " Bet won: <color=#00FF00>{0}</color> (<color=#00FF00>{1}</color>)",
                ["ExecutionTime"] = "You have <color=#FF0000>{0} minutes</color> to win the duel before you are executed.",
                ["FailedZone"] = "Failed to create a dueling zone, please try again.",
                ["FailedSetup"] = "Failed to setup the zone, please try again.",
                ["FailedRaycast"] = "Look towards the ground, and try again.",
                ["BetPlaced"] = "Your bet {0} ({1}) has been placed.",
                ["BetForfeitSuffix"] = " Type <color=#FFA500>/{0} bet forfeit</color> to forfeit your bet.",
                ["BetRefundSuffix"] = " Type <color=#FFA500>/{0} bet refund</color> to refund your bet.",
                ["BetNotEnough"] = "Bet cancelled. You do not have enough to bet this amount!",
                ["BetZero"] = "Bet cancelled. You do not have this item in your inventory.",
                ["DuelAnnouncement"] = "Type <color=#FFA500>/{duelChatCommand}</color> for information on the dueling system. See your standing on the leaderboard by using <color=#FFA500>/{ladderCommand}</color>. Type <color=#FFA500>/{queueCommand}</color> to enter the dueling queue now!",
                ["DuelAnnouncementBetsSuffix"] = " Feeling lucky? Use <color=#FFA500>/{0} bet</color> to create a bet!",
                ["ZoneCreated"] = "Dueling zone created successfully.",
                ["RemovedZone"] = "Removed dueling zone.",
                ["RemovedBan"] = "Unbanned {0}",
                ["AddedBan"] = "Banned {0}",
                ["PlayerNotFound"] = "{0} not found. Try being more specific or use a steam id.",
                ["RequestTimedOut"] = "Request timed out to duel <color=#00FF00>{0}</color>",
                ["RemovedFromQueueRequest"] = "You have been removed from the dueling queue since you have requested to duel another player.",
                ["RemovedFromDuel"] = "You have been removed from your duel.",
                ["BetsDoNotMatch"] = "Your bet {0} ({1}) does not match {2} ({3})",
                ["InvalidBet"] = "Invalid bet '{0}'",
                ["BetSyntax"] = "Syntax: /{0} bet <item> <amount> - resources must be refined",
                ["AvailableBets"] = "Available Bets:",
                ["MustHaveSameBet"] = "{0} is betting: {1} ({2}). You must have the same bet to duel this player.",
                ["NoBetsToRefund"] = "There are no bets to refund.",
                ["Disabled"] = "Disabled",
                ["HelpDuelBet"] = "<color=#C0C0C0><color=#FFA500>/{0} bet</color> - place a bet towards your next duel.</color>",
                ["HelpDuelAdmin"] = "<color=#FFA500>Admin: /{0} on|off</color> - enable/disable duels",
                ["HelpDuelAdminRefundAll"] = "<color=#FFA500>Admin: /{0} bet refundall</color> - refund all bets for all players",
                ["DuelsDisabledAlready"] = "Duels are already disabled!",
                ["DuelsNowDisabled"] = "Duels disabled. Sending duelers home.",
                ["DuelsEnabledAlready"] = "Duels are already enabled!",
                ["DuelsNowEnabled"] = "Duels enabled",
                ["NoBetsToClaim"] = "You have no bets to claim.",
                ["PlayerClaimedBet"] = "Claimed bet {0} ({1})",
                ["AllBetsClaimed"] = "You have claimed all of your bets.",
                ["DuelChatOff"] = "You will no longer see duel death messages.",
                ["DuelChatOn"] = "You will now see duel death messages.",
                ["PlayerRequestsAuto"] = "There is no requirement to allow duels on this server!",
                ["PlayerRequestsOn"] = "Players may now request to duel you. You will be removed from this list if you do not duel.",
                ["PlayerRequestsOff"] = "Players may no longer request to duel you.",
                ["BlockedRequestsFrom"] = "Blocked duel requests from: <color=#00FF00>{0}</color>",
                ["UnblockedRequestsFrom"] = "Removed block on duel requests from: <color=#00FF00>{0}</color>",
                ["AlreadyBlocked"] = "You have already blocked players from requesting duels.",
                ["NoBetsConfigured"] = "No bets are configured.",
                ["RefundAllPlayerNotice"] = "Server administrator has refunded your bet: {0} ({1})",
                ["RefundAllAdminNotice"] = "Refunded {0} ({1}): {2} ({3})",
                ["BetsRemaining"] = "Bet items remaining in database: {0}",
                ["AllBetsRefunded"] = "All dueling bets refunded",
                ["CannotForfeit"] = "You cannot forfeit bets on this server.",
                ["CannotForfeitRequestDuel"] = "You cannot forfeit a bet while requesting a duel!",
                ["CannotForfeitInDuel"] = "You cannot forfeit a bet while dueling!",
                ["CannotRefundRequestDuel"] = "You cannot refund a bet while requesting a duel!",
                ["CannotRefundInDuel"] = "You cannot refund a bet while dueling!",
                ["BetForfeit"] = "You forfeit your bet!",
                ["NoBetToForfeit"] = "You do not have an active bet to forfeit.",
                ["NoBetToRefund"] = "You do not have an active bet to refund.",
                ["CannotRefund"] = "You cannot refund bets on this server.",
                ["BetRefunded"] = "You have refunded your bet.",
                ["AlreadyBetting"] = "You are already betting! Your bet: {0} ({1})",
                ["ToRefundUse"] = "To refund your bet, type: <color=#FFA500>/{0} bet refund</color>",
                ["ToForfeitUse"] = "To forfeit your bet, type: <color=#FFA500>/{0} bet forfeit</color>. Refunds are not allowed.",
                ["InvalidNumber"] = "Invalid number: {0}",
                ["MultiplesOnly"] = "Number must be a multiple of 500. ie: 500, 1000, 2000, 5000, 10000, 15000",
                ["NoRequestsReceived"] = "No players have requested a duel with you.",
                ["DuelCancelledFor"] = "<color=#00FF00>{0}</color> has cancelled the duel!",
                ["NoPendingRequests"] = "You have no pending request to cancel.",
                ["DuelCancelledWith"] = "<color=#00FF00>{0}</color> has cancelled the duel request.",
                ["DuelCancelComplete"] = "Duel request cancelled.",
                ["MustWaitToRequestAgain"] = "You must wait <color=#FF0000>{0} minute(s)</color> from the last time you requested a duel to request another.",
                ["AlreadyDueling"] = "You are already dueling another player!",
                ["CannotRequestThisPlayer"] = "You are not allowed to request duels with this player.",
                ["TargetAlreadyDueling"] = "<color=#00FF00>{0}</color> is already dueling another player!",
                ["NotAllowedYet"] = "<color=#00FF00>{0}</color> has not enabled duel requests yet. They must type <color=#FFA500>/{1} allow</color>",
                ["MustWaitForAccept"] = "You have requested a duel with <color=#00FF00>{0}</color> already. You must wait for this player to accept the duel.",
                ["PendingRequestAlready"] = "This player has a duel request pending already.",
                ["TargetHasNoBet"] = "You have an active bet going. <color=#00FF00>{0}</color> must have the same bet to duel you.",
                ["YourBet"] = "Your bet: {0} ({1})",
                ["WoundedQueue"] = "You cannot duel while either player is wounded.",
                ["DuelMustBeNaked"] = "Duel cancelled: <color=#00FF00>{0}</color> inventory is not empty.",
                ["LadderLife"] = "<color=#5A625B>Use <color=#FFFF00>/{0} ladder life</color> to see all time stats</color>",
                ["EconomicsDeposit"] = "You have received <color=#FFFF00>${0}</color>!",
                ["ServerRewardPoints"] = "You have received <color=#FFFF00>{0} RP</color>!",
                ["DuelsMustBeEnabled"] = "Use '/{0} on' to enable dueling on the server.",
                ["DataSaved"] = "Data has been saved.",
                ["DuelsNowDisabledEmpty"] = "Duels disabled.",
                ["CannotTeleport"] = "You are not allowed to teleport from a dueling zone.",
                ["AllZonesFull"] = "All zones are currently full. Zones: {0}. Limit Per Zone: {1}",
                ["NoZoneFound"] = "No zone found. You must stand inside of the zone to remove it.",
                ["RemovedZoneAt"] = "Removed zone at {0}",
                ["CannotDuel"] = "You are not allowed to duel at the moment.",
                ["LeftZone"] = "<color=#FF0000>You were found outside of the dueling zone while dueling. Your items have been removed.</color>",
                ["SpawnAdd"] = "<color=#FFA500>/{0} spawns add</color> - add a spawn point at the position you are looking at.",
                ["SpawnHere"] = "<color=#FFA500>/{0} spawns here</color> - add a spawn point at your position.",
                ["SpawnRemove"] = "<color=#FFA500>/{0} spawns remove</color> - removes the nearest spawn point within <color=#FFA500>{1}m</color>.",
                ["SpawnRemoveAll"] = "<color=#FFA500>/{0} spawns removeall</color> - remove all spawn points within <color=#FFA500>{1}m</color>.",
                ["SpawnWipe"] = "<color=#FFA500>/{0} spawns wipe</color> - wipe all spawn points.",
                ["SpawnWiped"] = "<color=#FF0000>{0}</color> spawns points wiped.",
                ["SpawnCount"] = "<color=#008000>{0}</color> spawn points in database.",
                ["SpawnNoneFound"] = "No custom spawn points found within <color=#FFA500>{0}m</color>.",
                ["SpawnAdded"] = "Spawn point added at {0}",
                ["SpawnRemoved"] = "Removed <color=#FF0000>{0}</color> spawn(s)",
                ["SpawnExists"] = "This spawn point exists already.",
                ["SpawnNoneExist"] = "No spawn points exist.",
                ["ZoneExists"] = "A dueling zone already exists here.",
                ["ZoneLimit"] = "Zone limit reached ({0}). You must manually remove an existing zone before creating a new one.",
                ["CannotEventJoin"] = "You are not allowed to join this event while dueling.",
                ["KitDoesntExist"] = "This kit doesn't exist: {0}",
                ["KitSet"] = "Custom kit set to {0}. This kit will be used when both players have the same custom kit.",
                ["KitsNotConfigured"] = "No kits have been configured for dueling.",
                ["SupportCreated"] = "{0} new dueling zones were created, however the total amount was not met. Please lower the radius, increase Maximum Incline On Hills, or reload the plugin to try again.",
                ["SupportInvalidConfig"] = "Invalid zone radius detected in the configuration file for this map size. Please lower the radius, increase Maximum Incline On Hills, or reload the plugin to try again.",
                ["WallSyntax"] = "Use <color=#FFA500>/{0} walls [radius] <wood|stone></color>, or stand inside of an existing area with walls and use <color=#FFA500>/{0} walls</color> to remove them.",
                ["GeneratedWalls"] = "Generated {0} arena walls {1} high at {2} in {3}ms",
                ["ResetKit"] = "You are no longer using a custom kit.",
                ["HelpQueueInteract"] = "You cannot queue while unable to interact!",
                ["HelpDuels"] = "<color=#183a0e><size=18>DUELIST ({0})</size></color><color=#5A625B>\nDuel other players.</color>",
                ["HelpAllow"] = "<color=#5A397A>/{0} allow</color><color=#5A625B> • Toggle requests for duels</color>",
                ["HelpBlock"] = "<color=#5A397A>/{0} block <name></color><color=#5A625B> • Toggle block requests for a player</color>",
                ["HelpChallenge"] = "<color=#5A397A>/{0} <name></color><color=#5A625B> • Challenge another player</color>",
                ["HelpAccept"] = "<color=#5A397A>/{0} accept</color><color=#5A625B> • Accept a challenge</color>",
                ["HelpCancel"] = "<color=#5A397A>/{0} cancel</color><color=#5A625B> • Cancel your duel request</color>",
                ["HelpQueue"] = "<color=#5A397A>/{0}</color><color=#5A625B> • Join duel queue</color>",
                ["HelpChat"] = "<color=#5A397A>/{0} chat</color><color=#5A625B> • Toggle duel death messages</color>",
                ["HelpLadder"] = "<color=#5A397A>/{0} ladder</color><color=#5A625B> • Show top 10 duelists</color>",
                ["HelpBet"] = "<color=#5A397A>/{0} bet</color><color=#5A625B> • Place a bet towards a duel</color>",
                ["TopFormat"] = "<color=#666666><color=#5A625B>{0}.</color> <color=#00FF00>{1}</color> (<color=#008000>W:{2}</color> • <color=#ff0000>L:{3} </color> • <color=#4c0000>WLR:{4}</color>)</color>",
                ["NowDueling"] = "<color=#ff0000>You are now dueling <color=#00FF00>{0}</color>!</color>",
                ["MoneyRequired"] = "Both players must be able to pay an entry fee of <color=#008000>${0}</color> to duel.",
                ["CannotShop"] = "You are not allowed to shop while dueling.",
                ["DuelRequestSent"] = "Sent request to duel <color=#00FF00>{0}</color>. Request expires in 1 minute. Use <color=#FFA500>/{1} cancel</color> to cancel this request.",
                ["DuelRequestReceived"] = "<color=#00FF00>{0}</color> has requested a duel. You have 1 minute to type <color=#FFA500>/{1} accept</color> to accept the duel, or use <color=#FFA500>/{1} decline</color> to decline immediately.",
                ["MatchQueued"] = "You have entered the deathmatch queue. The match will start when a dueling zone becomes available.",
                ["MatchTeamed"] = "You are not allowed to do this while on a deathmatch team.",
                ["MatchNoMatchesExist"] = "No matches exist. Challenge a player by using <color=#FFA500>/{0} name</color>",
                ["MatchStarted"] = "Your match is starting versus: <color=#FFFF00>{0}</color>",
                ["MatchNextRound"] = "Round {0}/{1} is starting versus: <color=#FFFF00>{2}</color>",
                ["MatchStartedAlready"] = "Your match has already started. You must wait for it to end.",
                ["MatchPlayerLeft"] = "You have removed yourself from your deathmatch team.",
                ["MatchCannotChallenge"] = "{0} is already in a match.",
                ["MatchCannotChallengeAgain"] = "You can only challenge one player at a time.",
                ["MatchRequested"] = "<color=#00FF00>{0}</color> has requested a deathmatch. Use <color=#FFA500>/{1} accept</color> to accept this challenge.",
                ["MatchRequestSent"] = "Match request sent to <color=#00FF00>{0}</color>.",
                ["MatchNoneRequested"] = "No one has challenged you to a deathmatch yet.",
                ["MatchPlayerOffline"] = "The player challenging you is no longer online.",
                ["MatchSizeChanged"] = "Deathmatch changed to <color=#FFFF00>{0}v{0}</color>.",
                ["MatchOpened"] = "Your deathmatch is now open for private invitation. Friends may use <color=#FFA500>/{0} any</color>, and players may use <color=#FFA500>/{0} {1}</color> to join your team. Use <color=#FFA500>/{0} public</color> to toggle invitations as public or private.",
                ["MatchCancelled"] = "{0} has cancelled the deathmatch.",
                ["MatchNotAHost"] = "You must be a host of a deathmatch to use this command.",
                ["MatchDoesntExist"] = "You are not in a deathmatch. Challenge a player by using <color=#FFA500>/{0} name</color>.",
                ["MatchSizeSyntax"] = "Invalid syntax, use /{0} size #",
                ["MatchTeamFull"] = "Team is full ({0} players)",
                ["MatchJoinedTeam"] = "{0} joined {1} ({2}/{3}). {4} ({5}/{3})",
                ["MatchNoPlayersLeft"] = "No players are left on the opposing team. Match cancelled.",
                ["MatchChallenge2"] = "<color=#5A397A>/{0} any</color><color=#5A625B> • Join any match where a friend is the host</color>",
                ["MatchChallenge3"] = "<color=#5A397A>/{0} <code></color><color=#5A625B> • Join a match with the provided code</color>",
                ["MatchAccept"] = "<color=#5A397A>/{0} accept</color><color=#5A625B> • Accept a challenge</color>",
                ["MatchCancel"] = "<color=#5A397A>/{0} cancel</color><color=#5A625B> • Cancel your match request</color>",
                ["MatchLeave"] = "<color=#5A397A>/{0} cancel</color><color=#5A625B> • Leave your match</color>",
                ["MatchSize"] = "<color=#5A397A>/{0} size #</color><color=#5A625B> • Set your match size ({1}v{1}) [Hosts Only]</color>",
                ["MatchKickBan"] = "<color=#5A397A>/{0} kickban id/name</color><color=#5A625B> • Kickban a player from the match [Host Only]</color>",
                ["MatchSetCode"] = "<color=#5A397A>/{0} setcode [code]</color><color=#5A625B> • Change or see your code [Host Only]</color>",
                ["MatchTogglePublic"] = "<color=#5A397A>/{0} public</color><color=#5A625B> • Toggle match as public or private invitation [Host Only]</color>",
                ["MatchDefeat"] = "<color=#C0C0C0><color=#00FF00>{0}</color> has defeated <color=#00FF00>{1}</color> in a <color=#FFFF00>{2}v{2}</color> deathmatch!</color>",
                ["MatchIsNotNaked"] = "Match cannot start because <color=#00FF00>{0}</color> is not naked. Next queue check in 30 seconds.",
                ["MatchCannotBan"] = "You cannot ban this player, or this player is already banned.",
                ["MatchBannedUser"] = "You have banned <color=#00FF00>{0}</color> from your team.",
                ["MatchPlayerNotFound"] = "<color=#00FF00>{0}</color> is not on your team.",
                ["MatchCodeIs"] = "Your code is: {0}",
                ["InQueueList"] = "Players in the queue:",
                ["HelpTDM"] = "<color=#5A397A>/{0}</color><color=#5A625B> • Create a team deathmatch</color>",
                ["InMatchListGood"] = "Good Team: {0}",
                ["InMatchListEvil"] = "Evil Team: {0}",
                ["MatchNoTeamFoundCode"] = "No team could be found for you with the provided code: {0}",
                ["MatchNoTeamFoundAny"] = "No team could be found with a friend as the host. Use a code instead.",
                ["MatchPublic"] = "Your match is now open to the public.",
                ["MatchPrivate"] = "Your match is now private and requires a code, or to be a friend to join.",
                ["CannotBank"] = "You are not allowed to bank while dueling.",
                ["TargetMustBeNaked"] = "<color=#FF0000>The person you are challenging must be naked before you can challenge them.</color>",
                ["MatchKit"] = "<color=#5A397A>/{0} kit <name></color><color=#5A625B> • Changes the kit used [Host Only]</color>",
                ["MatchKitSet"] = "Kit set to: <color=#FFFF00>{0}</color>",
                ["MatchChallenge0"] = "<color=#5A397A>/{0} <name> [kitname]</color><color=#5A625B> • Challenge another player and set the kit if specified</color>",
                ["MatchDeathMessage1"] = "<color=#C0C0C0><color=#00FF00>{0}</color> <color=#000000>→</color> <color=#00FF00>{1}</color>: <color=#FFAA00>{2}</color> <color=#FFAA00>{3}: {4}m</color></color>",
                ["MatchDeathMessage2"] = "<color=#C0C0C0><color=#00FF00>{AttackerName}</color> (<color=#00FF00>W</color>: <color=#FFA500>{AttackerWins}</color> / <color=#FF0000>L</color>: <color=#FFA500>{AttackerLosses}</color>) <color=#000000>→</color> <color=#00FF00>{VictimName}</color> (<color=#00FF00>W</color>: <color=#FFA500>{VictimWins}</color> / <color=#FF0000>L</color>: <color=#FFA500>{VictimLosses}</color>): {Size}v{Size} <color=#FFAA00>{Weapon}</color> <color=#FFAA00>{Distance}m</color></color>",
                ["CommandNotAllowed"] = "You are not allowed to use this command right now.",
                ["HelpKit"] = "<color=#5A397A>/{0} kit</color><color=#5A625B> • Pick a kit</color>",
                ["ZonesSetup"] = "Initialized {0} existing dueling zones.",
                ["ArenasSetup"] = "{0} existing arenas are now protected.",
                ["NoPendingRequests2"] = "You have no pending request to accept.",
                ["MatchNoLongerValid"] = "You cannot join this match anymore.",
                ["NoMatchesExistYet"] = "No matches exist yet.",
                ["UI_Accept"] = "Accept",
                ["UI_Decline"] = "Decline",
                ["UI_Kits"] = "Kits",
                ["UI_Public"] = "Public",
                ["UI_Queue"] = "Queue",
                ["UI_TDM"] = "TDM",
                ["UI_TeamSize"] = "Set Team Size: ",
                ["UI_Any"] = "Exists",
                ["UI_Help"] = "<color=#5A397A>/{0}</color><color=#5A625B> • Show Duelist User Interface</color>",
                ["ResetSeed"] = "Stats for this seed have been reset.",
                ["RematchNone"] = "No rematches are available for you.",
                ["RematchNotify"] = "A rematch is available for {0} seconds. Click Ready to join, or type /{1} ready",
                ["UI_Ready"] = "Ready",
                ["RematchAccepted"] = "You have accepted the rematch.",
                ["RematchAcceptedAlready"] = "You have accepted the rematch already!",
                ["RematchTimedOut"] = "Your rematch timed out.",
                ["RematchFailed"] = "The rematch failed to start. Not all players were ready.",
                ["RematchFailed2"] = "The rematch failed to open. Not all players are available.",
                ["RematchAutoOn"] = "You will now automatically ready up for rematches.",
                ["RematchAutoOff"] = "You will no longer automatically ready up for rematches.",
                ["UI_Respawn"] = "Respawn",
                ["UI_Requeue"] = "Requeue",
                ["BeginSpectating"] = "You are now spectating.",
                ["EndSpectating"] = "You are no longer a spectator.",
                ["UI_ReadyOn"] = "<color=#FF0000>Ready On</color>",
                ["UI_ReadyOff"] = "Ready Off",
                ["SuicideBlock"] = "<color=#FF0000>You have suicided or disconnected in a duel and must wait up to 60 seconds to duel again.</color>",
                ["ZoneRenamed"] = "Zone renamed to {0}",
                ["ZoneNames"] = "<color=#183a0e>Zone Names ({0}):</color> {1}",
                ["ZoneRename"] = "/{0} rename <name>",
                ["ZoneSet"] = "Zone set to: {0}",
                ["Prefix"] = "[ <color=#406B35>Duelist</color> ]: ",
            }, this);
        }

        private Configuration config;

        public class Configuration
        {
            [JsonProperty(PropertyName = "Advanced Options")]
            public AdvancedSettings Advanced = new();

            [JsonProperty(PropertyName = "Animals")]
            public AnimalSettings Animals = new();

            [JsonProperty(PropertyName = "Automatically Power On Devices")]
            public DeviceSettings Devices = new();

            [JsonProperty(PropertyName = "Betting")]
            public BetSettings Betting = new();

            [JsonProperty(PropertyName = "Custom Kits")]
            public CustomKitSettings CustomKits = new();

            [JsonProperty(PropertyName = "Deathmatch")]
            public DeathmatchSettings Deathmatch = new();

            [JsonProperty(PropertyName = "Deployables")]
            public DeployableSettings Deployables = new();

            [JsonProperty(PropertyName = "Ranked Ladder")]
            public RankedSettings Ranked = new();

            [JsonProperty(PropertyName = "Respawn")]
            public RespawnSettings Respawn = new();

            [JsonProperty(PropertyName = "Rewards")]
            public RewardSettings Rewards = new();

            [JsonProperty(PropertyName = "Settings")]
            public PluginSettings Settings = new();

            [JsonProperty(PropertyName = "Spawns")]
            public SpawnSettings Spawns = new();

            [JsonProperty(PropertyName = "Spectators")]
            public SpectatorSettings Spectators = new();

            [JsonProperty(PropertyName = "User Interface")]
            public UserInterfaceSettings UserInterface = new();

            [JsonProperty(PropertyName = "Zone")]
            public ZoneSettings Zones = new();

            [JsonProperty(PropertyName = "Block paid and restricted content to comply with Facepunch TOS")]
            public bool BlockPaidContent = true;
        }

        private void LoadKitSettings()
        {
            config.Betting.Load();

            foreach (var kit in config.Settings.Kits)
            {
                if (!string.IsNullOrEmpty(kit) && !hpDuelingKits.Contains(kit))
                {
                    hpDuelingKits.Add(kit); // 0.1.14 fix
                    _hpDuelingKits.Add(kit); // 0.1.17 clone for Least Used Chance compatibility
                }
            }

            foreach (var kit in config.Settings.lesserKits)
            {
                if (!string.IsNullOrEmpty(kit) && !lpDuelingKits.Contains(kit))
                {
                    lpDuelingKits.Add(kit); // 0.1.16
                    _lpDuelingKits.Add(kit); // 0.1.17 clone for Least Used Chance compatibility
                }
            }
        }

        public class CustomKitSettings
        {
            [JsonProperty(PropertyName = "Use Workshop Skins")]
            public bool useWorkshopSkins = true;

            [JsonProperty("Kits", ObjectCreationHandling = ObjectCreationHandling.Replace, DefaultValueHandling = DefaultValueHandling.Populate)]

            public Dictionary<string, List<DuelKitItem>> Kits = new()
            {
                ["Hunting Bow"] = new List<DuelKitItem>
                {
                    new DuelKitItem(null, 1, "belt", null, "bow.hunting", 0, -1),
                    new DuelKitItem(null, 50, "belt", null, "arrow.wooden", 0, -1),
                    new DuelKitItem(null, 1, "belt", null, "spear.stone", 0, -1),
                    new DuelKitItem(null, 5, "belt", null, "bandage", 0, -1),
                    new DuelKitItem(null, 5, "belt", null, "syringe.medical", 0, -1),
                    new DuelKitItem(null, 5, "belt", null, "largemedkit", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "burlap.gloves", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "burlap.trousers", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "burlap.shoes", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "burlap.shirt", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "burlap.headwrap", 0, -1),
                },
                ["Assault Rifle and Bolt Action Rifle"] = new List<DuelKitItem>
                {
                    new DuelKitItem("ammo.rifle", 1, "belt", new() { "weapon.mod.lasersight" }, "rifle.ak", 0, -1),
                    new DuelKitItem(null, 1, "belt", new() { "weapon.mod.lasersight", "weapon.mod.small.scope" }, "rifle.bolt", 0, -1),
                    new DuelKitItem(null, 5, "belt", null, "bandage", 0, -1),
                    new DuelKitItem(null, 5, "belt", null, "syringe.medical", 0, -1),
                    new DuelKitItem(null, 5, "belt", null, "largemedkit", 0, -1),
                    new DuelKitItem(null, 10, "belt", null, "bearmeat.cooked", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "tshirt", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "metal.facemask", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "metal.plate.torso", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "pants", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "burlap.gloves", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "shoes.boots", 0, -1),
                    new DuelKitItem(null, 200, "main", null, "ammo.rifle", 0, -1),
                    new DuelKitItem(null, 1, "main", null, "weapon.mod.flashlight", 0, -1),
                    new DuelKitItem(null, 1, "main", null, "weapon.mod.small.scope", 0, -1),
                },
                ["Semi-Automatic Pistol"] = new List<DuelKitItem>
                {
                    new DuelKitItem("ammo.pistol", 1, "belt", new() { "weapon.mod.lasersight" }, "pistol.semiauto", 0, -1),
                    new DuelKitItem(null, 5, "belt", null, "bandage", 0, -1),
                    new DuelKitItem(null, 5, "belt", null, "syringe.medical", 0, -1),
                    new DuelKitItem(null, 5, "belt", null, "largemedkit", 0, -1),
                    new DuelKitItem(null, 10, "belt", null, "bearmeat.cooked", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "tshirt", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "metal.facemask", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "metal.plate.torso", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "pants", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "burlap.gloves", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "shoes.boots", 0, -1),
                    new DuelKitItem(null, 200, "main", null, "ammo.pistol", 0, -1),
                    new DuelKitItem(null, 1, "main", null, "weapon.mod.flashlight", 0, -1),
                },
                ["Pump Shotgun"] = new List<DuelKitItem>
                {
                    new DuelKitItem("ammo.shotgun.slug", 1, "belt", new() { "weapon.mod.lasersight" }, "shotgun.pump", 0, -1),
                    new DuelKitItem(null, 5, "belt", null, "bandage", 0, -1),
                    new DuelKitItem(null, 5, "belt", null, "syringe.medical", 0, -1),
                    new DuelKitItem(null, 5, "belt", null, "largemedkit", 0, -1),
                    new DuelKitItem(null, 10, "belt", null, "bearmeat.cooked", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "tshirt", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "metal.facemask", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "metal.plate.torso", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "pants", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "burlap.gloves", 0, -1),
                    new DuelKitItem(null, 1, "wear", null, "shoes.boots", 0, -1),
                    new DuelKitItem(null, 200, "main", null, "ammo.shotgun.slug", 0, -1),
                    new DuelKitItem(null, 1, "main", null, "weapon.mod.flashlight", 0, -1),
                }
            };
        }

        public class PluginSettings
        {
            [JsonProperty(PropertyName = "Allow Announcement")]
            public bool useAnnouncement = true;

            [JsonProperty(PropertyName = "Announce Duel Information Every X Seconds")]
            public float announceTime = 1800f;

            [JsonProperty(PropertyName = "Auto Create Dueling Zone If Zone Does Not Exist")]
            public bool autoSetup = false;

            [JsonProperty(PropertyName = "Auto Enable Dueling If Zone(s) Exist")]
            public bool autoEnable = true;

            [JsonProperty(PropertyName = "Auto Ready Is Always Enabled")]
            public bool autoReady = false;

            [JsonProperty(PropertyName = "Auto Wipe Dueling Zones On Map Wipe")]
            public bool wipeDuelZones = true;

            [JsonProperty(PropertyName = "Blacklist Commands")]
            public bool useBlacklistCommands = false;

            [JsonProperty(PropertyName = "Blacklisted Chat Commands", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> blacklistCommands = BlacklistedCommands;

            [JsonProperty(PropertyName = "Whitelist Commands")]
            public bool useWhitelistCommands = false;

            [JsonProperty(PropertyName = "Whitelisted Chat Commands", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> whitelistCommands = WhitelistedCommands;

            [JsonProperty(PropertyName = "Broadcast Defeat To All Players")]
            public bool broadcastDefeat = true;

            [JsonProperty(PropertyName = "Building Block Extension Radius")]
            public float buildingBlockExtensionRadius = 30f;

            [JsonProperty(PropertyName = "Ignored Player Items For Naked Check", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> ignoredNakedItems = new() 
            { 
                "apple", "apple.spoiled", "bearmeat", "blueberries", "cactusflesh", "can.beans", "can.tuna", "chicken.raw", 
                "chocolate", "corn", "deermeat.raw", "fish.raw", "granolabar", "grub", "horsemeat.raw", "humanmeat.raw", 
                "jar.pickle", "meat.boar", "potato", "pumpkin", "seed.corn", "seed.hemp", "seed.pumpkin", "smallwaterbottle", 
                "waterjug", "wolfmeat.raw", "worm", "rock", "torch", "torch.torch.skull", "divertorch" 
            };

            [JsonProperty(PropertyName = "Bypass Naked Check And Strip Items Anyway")]
            public bool bypassNewmans = false;

            [JsonProperty(PropertyName = "Chat SteamID")]
            public ulong chatSteamID = 0uL;

            [JsonProperty(PropertyName = "Disable Requirement To Allow Duels")]
            public bool autoAllowAll = false;

            [JsonProperty(PropertyName = "Create Dome Around Event Using Spheres (0 = disabled, recommended = 5)")]
            public int sphereAmount = 0;

            [JsonProperty(PropertyName = "Duel Command Name")]
            public string szDuelChatCommand = "duel";

            [JsonProperty(PropertyName = "Queue Command Name")]
            public string szQueueChatCommand = "queue";

            [JsonProperty(PropertyName = "Immunity Time")]
            public int immunityTime = 10;

            [JsonProperty(PropertyName = "Kits", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> Kits = DefaultKits;

            [JsonProperty(PropertyName = "Kits Least Used", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> lesserKits = DefaultLesserKits;

            [JsonProperty(PropertyName = "Kits Least Used Chance")]
            public float lesserKitChance = 0.25f;

            [JsonProperty(PropertyName = "No Stability On Structures")]
            public bool noStability = true;

            [JsonProperty(PropertyName = "No Movement During Immunity")]
            public bool noMovement = false;

            [JsonProperty(PropertyName = "Player Health After Duel [0 = disabled]")]
            public float playerHealth = 100f;

            [JsonProperty(PropertyName = "Prevent Players From Spawning In Zone")]
            public bool blockSpawning = true;

            [JsonProperty(PropertyName = "Prevent Players Not Dueling From Entering The Zone")]
            public bool removePlayers;

            [JsonProperty(PropertyName = "Prevent Players Includes Admins")]
            public bool removeAdmins;

            [JsonProperty(PropertyName = "Prevent Players Includes Noclip")]
            public bool removeFlying;

            [JsonProperty(PropertyName = "Reset Temporary Ladder Each Wipe")]
            public bool resetSeed = true;

            [JsonProperty(PropertyName = "Respawn Dead Players On Disconnect")]
            public bool respawnDeadDisconnect = true;

            [JsonProperty(PropertyName = "Respawn Zone Walls On Death")]
            public bool respawnWalls = false;

            [JsonProperty(PropertyName = "Scale Damage Percent", NullValueHandling = NullValueHandling.Ignore)]
            public float? _damageScaleAmount = null;

            [JsonProperty(PropertyName = "Scale Damage Multiplier")]
            public float damageScaleAmount = 1f;

            [JsonProperty(PropertyName = "Set Preferred Environment Plugin Time")]
            public bool setPlayerTime = false;

            [JsonProperty(PropertyName = "Use Invisibility")]
            public bool useInvisibility = true;

            [JsonProperty(PropertyName = "Time To Duel In Minutes Before Death")]
            public int deathTime = 10;

            [JsonProperty(PropertyName = "Use Random Skins")]
            public bool useRandomSkins = true;
        }

        public class AnimalSettings
        {
            [JsonProperty(PropertyName = "Die Instantly")]
            public bool killNpc = false;

            [JsonProperty(PropertyName = "Put To Sleep")]
            public bool putToSleep = true;
        }

        public class AdvancedSettings
        {
            [JsonProperty(PropertyName = "Let Players Die Normally")]
            public bool allowPlayerDeaths = false;

            [JsonProperty(PropertyName = "Require 1v1 Maximum Spawn Points To Be Less Than Or Equal To X")]
            public int requiredMaxSpawns = 200;

            [JsonProperty(PropertyName = "Require 1v1 Minimum Spawn Points To Be Equal Or Greater Than X")]
            public int requiredMinSpawns = 2;

            [JsonProperty(PropertyName = "Require TDM Minimum Spawn Points To Be Equal Or Greater To The Number Of Players Joining")]
            public bool requireTeamSize = false;

            [JsonProperty(PropertyName = "Send Dead Players Back Home")]
            public bool sendDeadHome = true;

            [JsonProperty(PropertyName = "Send Defeated Players Back Home")]
            public bool sendDefeatedHome = false;
        }

        public class BetSettings
        {
            [JsonProperty(PropertyName = "Allow Bets To Be Forfeit")]
            public bool allowBetForfeit = true;

            [JsonProperty(PropertyName = "Allow Bets To Be Refunded")]
            public bool allowBetRefund = false;

            [JsonProperty(PropertyName = "Bets", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<object> entries = DefaultBets;

            internal List<BetInfo> Bets = new();

            internal void Load()
            {
                foreach (var entry in entries)
                {
                    Bets.Add(JsonConvert.DeserializeObject<BetInfo>(JsonConvert.SerializeObject(entry)));
                }
            }

            [JsonProperty(PropertyName = "Enabled")]
            public bool allowBets = false;
        }

        public class DeathmatchSettings
        {
            [JsonProperty(PropertyName = "Announce Deaths To Server")]
            public bool tdmServerDeaths = false;

            [JsonProperty(PropertyName = "Announce Deaths To Match")]
            public bool tdmMatchDeaths = true;

            [JsonProperty(PropertyName = "Chat Command")]
            public string szMatchChatCommand = "tdm";

            [JsonProperty(PropertyName = "Enabled")]
            public bool tdmEnabled = true;

            [JsonProperty(PropertyName = "Friendly Fire")]
            public bool dmFF = true;

            [JsonProperty(PropertyName = "Rounds per match")]
            public int Rounds = 3;

            [JsonProperty(PropertyName = "Prioritize closer teams spawns first")]
            public bool jitteredSpawns = true;

            [JsonProperty(PropertyName = "Min Team Size")]
            public int minDeathmatchSize = 2;

            [JsonProperty(PropertyName = "Max Team Size")]
            public int maxDeathmatchSize = 5;

            [JsonProperty(PropertyName = "Evil Shirt Skin")]
            public ulong teamEvilShirt = 14177;

            [JsonProperty(PropertyName = "Good Shirt Skin")]
            public ulong teamGoodShirt = 101;

            [JsonProperty(PropertyName = "Shirt Shortname")]
            public string teamShirt = "tshirt";

            [JsonProperty(PropertyName = "Economics Money [0 = disabled]")]
            public double teamEconomicsMoney;

            [JsonProperty(PropertyName = "ServerRewards Points [0 = disabled]")]
            public int teamServerRewardsPoints;
        }

        public class DeployableSettings
        {
            [JsonProperty(PropertyName = "Allowed", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public Dictionary<string, bool> Allowed = new();

            [JsonProperty(PropertyName = "Morph Barricades Into High External Stone Walls")]
            public bool morphBarricadesStoneWalls;

            [JsonProperty(PropertyName = "Morph Barricades Into High External Wooden Walls")]
            public bool morphBarricadesWoodenWalls;
        }

        public class DeviceSettings
        {
            [JsonProperty(PropertyName = "AutoTurrets")]
            public bool autoTurrets = false;

            [JsonProperty(PropertyName = "FlameTurrets")]
            public bool autoFlames = false;

            [JsonProperty(PropertyName = "Ovens")]
            public bool autoOvens = false;
        }

        public class RankedSettings
        {
            [JsonProperty(PropertyName = "Award Top X Players On Wipe")]
            public int permsToGive = 3;

            [JsonProperty(PropertyName = "Enabled")]
            public bool recordStats = true;
        }

        public class RespawnSettings
        {
            [JsonProperty(PropertyName = "Give Kit If Respawn Items Are Empty")]
            public string autoKitName = "autokit";

            [JsonProperty("Items", ObjectCreationHandling = ObjectCreationHandling.Replace, DefaultValueHandling = DefaultValueHandling.Populate)]
            public List<DuelKitItem> respawnLoot { get; set; } = new List<DuelKitItem>
            {
                new DuelKitItem(null, 1, "belt", null, "rock", 0, -1),
                new DuelKitItem(null, 1, "belt", null, "torch", 0, -1),
            };
        }

        public class RewardSettings
        {
            [JsonProperty(PropertyName = "Economics Money [0 = disabled]")]
            public double economicsMoney;

            [JsonProperty(PropertyName = "ServerRewards Points [0 = disabled]")]
            public int serverRewardsPoints;

            [JsonProperty(PropertyName = "Payment Required To Duel")]
            public CustomCostOption requiredDuelPaymentOption = new();
        }

        public class SpawnSettings
        {
            [JsonProperty(PropertyName = "Auto Remove On Zone Removal")]
            public bool spAutoRemove = false;

            [JsonProperty(PropertyName = "Draw Time")]
            public float spDrawTime = 30f;

            [JsonProperty(PropertyName = "Remove All Distance")]
            public float spRemoveAllMaxDistance;

            [JsonProperty(PropertyName = "Remove Distance")]
            public float spRemoveOneMaxDistance = 10f;
        }

        public class SpectatorSettings
        {
            [JsonProperty(PropertyName = "Send Home If Rematch Times Out")]
            public bool sendHomeSpectatorWhenRematchTimesOut = false;
        }

        public class UserInterfaceSettings
        {
            [JsonProperty(PropertyName = "Auto Enable GUI For Players")]
            public bool guiAutoEnable = false;

            [JsonProperty(PropertyName = "Chat Command")]
            public string szUIChatCommand = "dui";

            [JsonProperty(PropertyName = "Send Spectators Home FirstOrDefault When Clicking Requeue")]
            public bool sendHomeRequeue = false;

            [JsonProperty(PropertyName = "Show Close Button (X)")]
            public bool guiUseCloseButton = true;

            [JsonProperty(PropertyName = "Show Defeat Message UI For X Seconds")]
            public float guiAnnounceUITime = 7.5f;

            [JsonProperty(PropertyName = "Use Cursor")]
            public bool guiUseCursor = false;
        }

        public class ZoneSettings
        {
            [JsonProperty(PropertyName = "Avoid Creating Automatic Spawn Points In Water")]
            public bool avoidWaterSpawns = true;

            [JsonProperty(PropertyName = "Create Least Amount Of Walls")]
            public bool useLeastAmount = false;

            [JsonProperty(PropertyName = "Create New Zone Every X Duels [0 = disabled]")]
            public int zoneCounter = 10;

            [JsonProperty(PropertyName = "Extra High External Wall Stacks")]
            public int extraWallStacks = 2;

            [JsonProperty(PropertyName = "Max Zones [Min 1]")]
            public int zoneAmount = 1;

            [JsonProperty(PropertyName = "Maximum Incline On Hills")]
            public float maxIncline = 40f;

            [JsonProperty(PropertyName = "Players Per Zone [Multiple Of 2]")]
            public int playersPerZone = 10;

            [JsonProperty(PropertyName = "Players Visible To Admins")]
            public bool visibleToAdmins = true;

            [JsonProperty(PropertyName = "Use Arena Wall Generation")]
            public bool useZoneWalls = true;

            [JsonProperty(PropertyName = "Use Wooden Walls")]
            public bool zoneUseWoodenWalls = false;

            [JsonProperty(PropertyName = "Zone Radius (Min: 50, Max: 300)")]
            public float zoneRadius = 50f;

            [JsonProperty(PropertyName = "Allowed Zone Manager Zones", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> Allowed = new();
        }

        private const bool en = true;
        public class CustomCostOption
        {
            [JsonProperty(PropertyName = en ? "Enabled" : "Включено")] public bool Enabled = true; 
            [JsonProperty(en ? "Plugin Name" : "Название плагина")] public string PluginName = "Economics";
            [JsonProperty(en ? "Deposit Method (API)" : "Название метода(API)")] public string DepositHookName = "Deposit";
            [JsonProperty(en ? "Withdraw Method (API)" : "Метод вывода средств (API)")] public string WithdrawHookName = "Withdraw";
            [JsonProperty(en ? "Balance Method (API)" : "Метод балансировки (API)")] public string BalanceHookName = "Balance";
            [JsonProperty("ShoppyStock Shop Name")] public string ShoppyStockShopName = "";
            [JsonProperty(en ? "Currency Name" : "Название валюты")] public string CurrencyName = "$";
            [JsonProperty(en ? "Amount" : "Сумма")] public double Amount;
            [JsonProperty(en ? "Amount Data Type (API) - [ 0 - double | 1 - float | 2 - int ]" : "Тип данных метода(Сумма API) - [ 0 - double | 1 - float | 2 - int ]")] public int AmountDataType;
            [JsonProperty(en ? "User Data Type (API) - [ 0 - ulong | 1 - string | 2 - player ]" : "Тип данных метода(User API) - [ 0 - ulong | 1 - string | 2 - player ]")] public int PlayerDataType;

            internal Plugin plugin;
            internal bool IsEnabled() => Enabled && Amount > 0 && !string.IsNullOrWhiteSpace(PluginName) && !string.IsNullOrWhiteSpace(WithdrawHookName) && !string.IsNullOrWhiteSpace(DepositHookName) && !string.IsNullOrWhiteSpace(BalanceHookName);
        }

        public List<string> VerifiedKits
        {
            get
            {
                VerifyKits();

                var list = new List<string>();

                if (hpDuelingKits.Count > 0)
                    list.AddRange(hpDuelingKits);

                if (lpDuelingKits.Count > 0)
                    list.AddRange(lpDuelingKits);

                if (list.Count == 0 && config.CustomKits.Kits.Count > 0)
                {
                    list.AddRange(config.CustomKits.Kits.Keys);
                }

                list.Sort();
                return list;
            }
        }

        public string GetVerifiedKit(string kit)
        {
            string kits = string.Join(", ", VerifiedKits);

            if (!string.IsNullOrEmpty(kits))
            {
                foreach (var entry in config.CustomKits.Kits)
                {
                    if (entry.Key.Equals(kit, StringComparison.CurrentCultureIgnoreCase))
                    {
                        return entry.Key;
                    }
                }
                foreach (var entry in hpDuelingKits)
                {
                    if (entry.Equals(kit, StringComparison.CurrentCultureIgnoreCase))
                    {
                        return entry;
                    }
                }
                foreach (var entry in lpDuelingKits)
                {
                    if (entry.Equals(kit, StringComparison.CurrentCultureIgnoreCase))
                    {
                        return entry;
                    }
                }
            }

            return null;
        }

        private bool isInitialized = true;

        protected override void LoadConfig()
        {
            base.LoadConfig();
            isInitialized = false;
            try
            {
                config = Config.ReadObject<Configuration>();
                if (config == null) throw new NullReferenceException("config");
                isInitialized = true;
            }
            catch (Exception ex)
            {
                LoadDefaultConfig();
                Puts(ex.ToString());
            }
            LoadKitSettings();
            EnsureLimits();
            SaveConfig();
        }

        protected override void SaveConfig()
        {
            if (isInitialized)
            {
                Config.WriteObject(config);
            }
        }

        private void RegisterCommands()
        {
            if (recordStats)
            {
                if (!permission.PermissionExists(duelistPerm)) // prevent warning
                    permission.RegisterPermission(duelistPerm, this);

                permission.CreateGroup(duelistGroup, duelistGroup, 0);
                permission.GrantGroupPermission(duelistGroup, duelistPerm, this);
            }

            AddCovalenceCommand("duelist", nameof(CommandDuelist));

            if (!string.IsNullOrEmpty(config.Settings.szDuelChatCommand))
            {
                AddCovalenceCommand(config.Settings.szDuelChatCommand, nameof(CommandDuelist));
                whitelistCommands.Add(config.Settings.szDuelChatCommand.ToLower());
            }

            if (!string.IsNullOrEmpty(config.Settings.szQueueChatCommand))
            {
                AddCovalenceCommand(config.Settings.szQueueChatCommand, nameof(CommandQueue));
                whitelistCommands.Add(config.Settings.szQueueChatCommand.ToLower());
            }

            if (config.Deathmatch.tdmEnabled && !string.IsNullOrEmpty(config.Deathmatch.szMatchChatCommand))
            {
                AddCovalenceCommand(config.Deathmatch.szMatchChatCommand, nameof(CommandDeathmatch));
                whitelistCommands.Add(config.Deathmatch.szMatchChatCommand.ToLower());
            }

            if (!string.IsNullOrEmpty(config.UserInterface.szUIChatCommand))
            {
                cmd.AddChatCommand(config.UserInterface.szUIChatCommand, this, cmdDUI);
                cmd.AddConsoleCommand(config.UserInterface.szUIChatCommand, this, nameof(ccmdDUI));
            }
        }

        private void EnsureLimits()
        {
            if (config.Settings.buildingBlockExtensionRadius < 20f)
                config.Settings.buildingBlockExtensionRadius = 20f;

            if (config.Zones.zoneAmount < 1)
                config.Zones.zoneAmount = 1;

            if (config.Zones.playersPerZone < 2)
                config.Zones.playersPerZone = 2;
            else if (config.Zones.playersPerZone % 2 != 0)
                config.Zones.playersPerZone++;

            if (config.Settings.immunityTime < 0)
                config.Settings.immunityTime = 0;

            if (config.Zones.zoneRadius < 50f)
                config.Zones.zoneRadius = 50f;
            else if (config.Zones.zoneRadius > 300f)
                config.Zones.zoneRadius = 300f;

            if (config.Advanced.requiredMinSpawns < 2)
                config.Advanced.requiredMinSpawns = 2;

            if (config.Advanced.requiredMaxSpawns < 2)
                config.Advanced.requiredMaxSpawns = 2;

            if (config.UserInterface.guiAnnounceUITime < 1f)
                config.UserInterface.guiAnnounceUITime = 1f;

            if (config.Settings._damageScaleAmount != null)
            {
                config.Settings.damageScaleAmount = config.Settings._damageScaleAmount.Value;
                config.Settings._damageScaleAmount = null;
            }

            whitelistCommands.AddRange(config.Settings.whitelistCommands);
        }

        private void SetupDefinitions()
        {
            if (!isInitialized) return;
            using var newlyAdded = GetPooledList<string>();
            using var defs = GetPooledList<ItemDefinition>();
            defs.AddRange(ItemManager.GetItemDefinitions());
            defs.Sort((a, b) => string.Compare(a.displayName.english, b.displayName.english, StringComparison.Ordinal));
            foreach (var itemDef in defs)
            {
                var mod = itemDef.GetComponent<ItemModDeployable>();
                if (mod == null)
                {
                    continue;
                }

                bool externalWall = mod.entityPrefab.resourcePath.Contains("external") && mod.entityPrefab.resourcePath.Contains("wall");
                bool barricade = mod.entityPrefab.resourcePath.Contains("barricade");
                bool isLadder = mod.entityPrefab.resourcePath.Contains("ladder.wooden.wall");

                if (externalWall || barricade || isLadder)
                {
                    if (config.Deployables.Allowed.TryAdd(itemDef.displayName.english, true))
                    {
                        newlyAdded.Add(itemDef.displayName.english);
                    }
                }

                prefabs[mod.entityPrefab.resourcePath] = itemDef.displayName.translated;
            }
            if (newlyAdded.Count > 0)
            {
                Puts("Configuration file has been updated with: {0}", string.Join(", ", newlyAdded));
                SaveConfig();
            }
        }

        protected override void LoadDefaultConfig()
        {
            PrintWarning("Creating a new configuration file");
            config = new();
        }

        private Dictionary<string, string> hexColors = new Dictionary<string, string>
        {
            ["<color=blue>"] = "<color=#0000FF>",
            ["<color=red>"] = "<color=#FF0000>",
            ["<color=yellow>"] = "<color=#FFFF00>",
            ["<color=lightblue>"] = "<color=#ADD8E6>",
            ["<color=orange>"] = "<color=#FFA500>",
            ["<color=silver>"] = "<color=#C0C0C0>",
            ["<color=magenta>"] = "<color=#FF00FF>",
            ["<color=green>"] = "<color=#008000>",
            ["<color=lime>"] = "<color=#00FF00>",
        };

        private string msg(string key, string id = null, params object[] args)
        {
            using var sb = DisposableBuilder.Get();

            if (id == null)
            {
                sb.Append(RemoveFormatting(lang.GetMessage(key, this, id)));
            }
            else sb.Append(lang.GetMessage(key, this, id));

            if (sb.Length == 0)
            {
                return string.Empty;
            }

            foreach (var pair in hexColors)
            {
                sb.Replace(pair.Key, pair.Value);
            }

            return args.Length > 0 ? string.Format(sb.ToString(), args) : sb.ToString();
        }

        public Regex TagRegex = new("<.*?>", RegexOptions.Compiled);
        public string RemoveFormatting(string source)
        {
            return source.Contains('>') ? TagRegex.Replace(source, string.Empty) : source;
        }

        public void MessageAll(IEnumerable<BasePlayer> players, string key, params object[] args)
        {
            foreach (var player in players)
            {
                if (IsNotConnected(player)) continue;
                Player.Message(player, msg(key, player.UserIDString, args), chatSteamID);
            }
        }

        public void Message(BasePlayer player, string key, params object[] args)
        {
            if (player != null && key != null)
            {
                if (player.IsConnected) Player.Message(player, msg(key, player.UserIDString, args), chatSteamID);
                //if (player is DuelistNPC) Puts(msg(key, player.UserIDString, args));
            }
        }

        public void Message(IPlayer user, string key, params object[] args)
        {
            if (user.Object is BasePlayer player)
            {
                Message(player, key, args);
            }
            else user.Reply(msg(key, user.Id, args));
        }

        public void MessageB(BasePlayer player, string message)
        {
            if (player != null && player.IsConnected)
            {
                Player.Message(player, message, chatSteamID);
            }
        }

        protected static void Puts(Exception ex)
        {
            Interface.Oxide.LogInfo("[{0}] {1}", "Duelist", ex);
        }

        protected new static void Puts(string format, params object[] args)
        {
            if (!string.IsNullOrWhiteSpace(format))
            {
                Interface.Oxide.LogInfo("[{0}] {1}", "Duelist", (args.Length != 0) ? string.Format(format, args) : format);
            }
        }

        #endregion
    }
}

namespace Oxide.Plugins.DuelistExtensionMethods
{
    public static class ExtensionMethods
    {
        public class DisposableBuilder : IDisposable, Pool.IPooled
        {
            private StringBuilder _builder;
            public DisposableBuilder() { }
            public void LeavePool() => _builder = Pool.Get<StringBuilder>();
            public void EnterPool() => Pool.FreeUnmanaged(ref _builder);
            public void Dispose() { DisposableBuilder obj = this; Pool.Free(ref obj); }
            public static DisposableBuilder Get() => Pool.Get<DisposableBuilder>();
            public DisposableBuilder Append(string value) { _builder.Append(value); return this; }
            public DisposableBuilder Replace(string oldValue, string newValue) { _builder.Replace(oldValue, newValue); return this; }
            public override string ToString() => _builder.ToString();
            public int Length { get => _builder.Length; set => _builder.Length = value; }
        }
        public static void RemoveWhere<K, V>(this Dictionary<K, V> a, Func<K, V, bool> b) { using var c = Facepunch.Pool.Get<PooledList<K>>(); foreach (var d in a) { if (b(d.Key, d.Value)) c.Add(d.Key); } foreach (var e in c) a.Remove(e); }
        public static void RemoveWhere<TKey, TValue>(this Dictionary<TKey, TValue> a, Func<TKey, bool> b) => RemoveWhere(a, (key, val) => b(key));
        public static void RemoveWhere<TKey, TValue>(this Dictionary<TKey, TValue> a, Func<TValue, bool> b) => RemoveWhere(a, (key, val) => b(val));
        public static bool All<T>(this IEnumerable<T> a, Func<T, bool> b) { using (var c = a.GetEnumerator()) { while (c.MoveNext()) { if (!b(c.Current)) { return false; } } } return true; }
        public static T ElementAt<T>(this IEnumerable<T> a, int b) { using (var c = a.GetEnumerator()) { while (c.MoveNext()) { if (b == 0) { return c.Current; } b--; } } return default(T); }
        public static bool Exists<T>(this IEnumerable<T> a, Func<T, bool> b = null) { using var c = a.GetEnumerator(); while (c.MoveNext()) { if (b == null || b(c.Current)) { return true; } } return false; }
        public static T FirstOrDefault<T>(this IEnumerable<T> a, Func<T, bool> b = null) { using var c = a.GetEnumerator(); while (c.MoveNext()) { if (b == null || b(c.Current)) { return c.Current; } } return default; }
        public static int Count<T>(this IEnumerable<T> a, Func<T, bool> b = null) { int c = 0; foreach (T d in a) { if (b == null || b(d)) { c++; } } return c; }
        public static IEnumerable<T> Select<Y, T>(this IList<Y> a, Func<Y, T> b) { for (int i = 0; i < a.Count; i++) { yield return b(a[i]); } }
        public static string[] Skip(this string[] a, int b) { if (a.Length == 0) { return Array.Empty<string>(); } string[] c = new string[a.Length - b]; int n = 0; for (int i = 0; i < a.Length; i++) { if (i < b) continue; c[n] = a[i]; n++; } return c; }
        public static IEnumerable<V> Select<T, V>(this IEnumerable<T> a, Func<T, V> b) { using var c = a.GetEnumerator(); while (c.MoveNext()) { yield return b(c.Current); } }
        public static IEnumerable<T> Take<T>(this IEnumerable<T> a, int b) { if (a == null) yield break; int i = 0; foreach (T c in a) { if (i++ < b) yield return c; else break; } }
        public static IEnumerable<T> Where<T>(this IEnumerable<T> a, Func<T, bool> b) { using var c = a.GetEnumerator(); while (c.MoveNext()) { if (b(c.Current)) yield return c.Current; } }
        public static List<T> ToList<T>(this IEnumerable<T> a) => new(a);
        public static string ObjectName(this Collider collider) { try { return collider.name ?? string.Empty; } catch { return string.Empty; } }
        public static bool IsHuman(this BasePlayer a) => a != null && a.userID.IsSteamId();
        public static bool IsNullOrEmpty<T>(this IReadOnlyCollection<T> c) => c == null || c.Count == 0; 
        public static int Sum<T>(this IEnumerable<T> a, Func<T, int> b) { int c = 0; foreach (T d in a) { c += b(d); } return c; }
        public static bool IsKilled(this BaseNetworkable a) => a == null || a.IsDestroyed || !a.IsFullySpawned();
        public static void DelayedSafeKill(this BaseNetworkable a) { if (!a.IsKilled()) a.Invoke(a.SafelyKill, 0.0625f); }
        public static void SafelyKill(this BaseNetworkable a) { if (a == null || a.IsDestroyed) { return; } a.Kill(BaseNetworkable.DestroyMode.None); }
        public static bool CanCall(this Plugin a) { return a != null && a.IsLoaded; }
    }
}