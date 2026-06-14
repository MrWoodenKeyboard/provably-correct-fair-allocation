# Foundational Rocq Definitions for Temporal Fair Allocation

## 1. Context Variables
- `n`: Number of agents.
- `m`: Total number of items.
- `T`: Number of days (time steps).

## 2. Basic Entities
- `agent := fin n` (The type of a single agent)
- `item := fin m` (The type of a single item)
- `bundle := gset item` (A set of items)
- `valuation_function := agent -> item -> nat` (Agent's value for an item)

## 3. Instances and Allocations
- **`static_instance`**: A record for a single problem instance (items + valuations).
- **`allocation S`**: A disjoint and complete partition of item set `S`.
- **`temporal_instance`**: A sequence of static instances over `T` days.
- **`temporal_allocation inst`**: A sequence of allocations, one for each day.

## 4. Cumulative Concepts
- **`cumulative_bundle inst A t i`**: Everything agent `i` owns up to day `t`.
- **`cumulative_instance inst t`**: The combined problem state up to day `t`.
