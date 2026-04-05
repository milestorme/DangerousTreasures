# DangerousTreasures (Performance Edition)

**DangerousTreasures** is a dynamic PvP event plugin for Rust that spawns high-value loot crates across the map, guarded by hostile NPCs and environmental hazards. Players must fight their way to the event, survive the chaos, and secure the treasure before others do.

Originally created by nivex, this version includes **performance-focused improvements and optimized defaults** for better server stability.

---

## 🔥 Features

- Automated treasure events at configurable intervals  
- Randomized spawn locations across the map  
- Locked loot crate with countdown before opening  
- PvP hotspot encouraging player conflict  
- Hostile NPCs guarding the event  
- Optional rockets, fire effects, and event hazards  
- Map markers and player tracking commands  
- Ranked ladder system with wipe-based rewards  
- Highly configurable loot tables and event behavior  
- Built-in zone system (no dependency required)

---

## ⚡ Performance Optimizations (This Version)

- Reduced high-frequency timers (NPC AI, tracking, missiles)  
- Optimized player tracking (NewmanTracker only runs when needed)  
- Lower default NPC counts and aggression ranges  
- Reduced rocket count and event spam  
- Disabled heavy features (fire aura, skins) by default  
- Improved cleanup and reduced unnecessary processing  

---

## 🎮 How It Works

1. The plugin automatically spawns an event every configured interval  
2. A treasure crate appears at a random location  
3. Rockets and effects mark the event location  
4. NPCs guard the crate  
5. The crate remains locked for a set time  
6. Players fight to control the area  
7. The crate unlocks and can be looted  
8. The event ends once the loot is taken  

---

## 🔐 Permissions

| Permission | Description |
|----------|-------------|
| dangeroustreasures.use | Allows players to start events |
| dangeroustreasures.th | Awarded to top players on wipe |
| dangeroustreasures.notitle | Hides ranked titles |

---

## 💬 Chat Commands

| Command | Description |
|--------|------------|
| /dtevent | Start an event |
| /dtevent tp | Start event and teleport (admin) |
| /dtevent me | Spawn event at your position |
| /dtevent custom | Set/remove custom spawn |
| /dtevent help | Show help and monument list |
| /dtd | Show event status/distance |
| /dtd tp | Teleport to event (admin) |
| /dtd ladder | Show leaderboard |
| /dtd lifetime | Show lifetime stats |

---

## 🖥️ Console Commands

dtevent

Starts an event from the server console.

---

## ⚙️ Configuration Overview

The plugin is fully configurable via:

/oxide/config/DangerousTreasures.json

---

## 🚀 Installation

1. Download the plugin  
2. Upload to:
/oxide/plugins/  
3. Start or restart your server  
4. Edit config in:
/oxide/config/  

---

## 🧠 Performance Tips

- Disable Fireballs if not needed  
- Reduce rocket count  
- Keep NPC counts low (2–4 recommended)  
- Lower aggression range (30–50)  
- Avoid unnecessary UI/marker spam  

---

## 🏆 Ranked Ladder

- Tracks player performance across events  
- Awards top players on wipe  
- Supports lifetime and wipe-based stats  

---

## 📌 Notes

- Designed for high-intensity PvP encounters  
- Suitable for small to large servers  
- Highly customizable for PvE or PvP  

---

## 📜 License

Based on the original DangerousTreasures plugin by nivex.  
Modified for performance and improved defaults.

---

## ✅ Summary

DangerousTreasures adds a high-risk, high-reward PvP event system to your Rust server, now optimized for performance and scalability.

## Credits

- Original Author ***https://umod.org/user/nivex***
- Performance updates *** Milestorme***