# Core Objective: Temporal EF1 Verification of a Greedy Allocator
**Goal:** Mechanize and verify an online fair allocation algorithm using Rocq, HeapLang, and Iris separation logic.

### 1. Architectural Scope
- **Foundational Math (Maximum Generality):** The base Rocq definitions for agents, items, bundles, and valuations are completely general (additive valuations over `nat`, arbitrary arrivals).
- **Theorems (Restricted Context):** The specific proofs for the online allocation algorithm will introduce constraints purely as logical hypotheses:
  - `single_item_arrival`: Exactly 1 item arrives each day.
  - `binary_valuation`: $V_i(o) \in \{0, 1\}$.
- **Libraries:** Use `stdpp` natively for finite maps/sets to maintain seamless compatibility with Iris.

### 2. The Algorithm: Lowest Cumulative Utility (Greedy)
Starting on day 0, when a single item arrives:
1. Identify the subset of agents who value the item positively ($V_i(o) > 0$).
2. If the subset is empty, assign the item to an arbitrary agent (e.g., agent 0).
3. If the subset is non-empty, assign the item to the agent in the subset with the strictly lowest current cumulative utility. Ties can be broken arbitrarily.

### 3. Rigorous Roadmap

#### Phase 1: Pure Functional Implementation & Verification (Rocq)
1. **Constraints:** Formalize `single_item_arrival` and `binary_valuation` in `Foundations.v`.
2. **Pure Algorithm:** Implement the greedy algorithm as a pure Rocq function `greedy_allocator : temporal_instance -> temporal_allocation`.
3. **Pure Correctness:** Prove the pure function produces a structurally valid allocation.
4. **Pure Fairness (The Core Math):** Prove `Theorem greedy_is_TEF1`: 
   `single_item_arrival inst -> binary_valuation inst -> TEF1 inst (greedy_allocator inst)`.

#### Phase 2: Physical Implementation (HeapLang)
1. **Data Structures:** Define the physical state in HeapLang. We will likely need:
   - An array/list of size `n` storing the current cumulative utilities of all agents.
   - An array/list recording the allocation map (which agent received which item).
2. **Program:** Write the `greedy_alloc_prog` in HeapLang that iterates over the arrival sequence, reading/updating utilities and the allocation map.

#### Phase 3: Separation Logic Verification (Iris)
1. **Representation Predicate:** Define `is_alloc_state (A : temporal_allocation)` linking the physical HeapLang arrays to the pure Rocq allocation state.
2. **Hoare Triple:** Formulate and prove the refinement:
   ```coq
   {{{ is_alloc_state A_prev * ⌜single_item_arrival inst⌝ * ⌜binary_valuation V⌝ }}} 
     greedy_alloc_prog inst 
   {{{ RET (); is_alloc_state (greedy_allocator inst) }}}
   ```
3. **Final Synthesis:** Combine the Hoare triple with `greedy_is_TEF1` to prove the executed code results in a TEF1 fair state.
