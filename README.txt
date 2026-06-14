CS 472 Final Project: Mechanizing Temporal Fair Allocation
Ali Eser

This project presents the formal verification of an online fair allocation algorithm in Rocq. The goal is to prove that a greedy allocation rule maintains Temporal Envy-Freeness up to One Item (TEF1) in instances with binary, constant valuations.

### Project Overview
The project was motivated by the challenge of translating game-theoretic fairness concepts into formal proofs. As described in my initial proposal, the vision was to create a tool for reasoning about temporal instances—where items arrive sequentially over time. 

My mid-semester check-in highlighted the architectural struggles of this translation. I eventually moved away from complex, proof-carrying Records in favor of a recursive functional model. This shift provided the necessary "transparency" for Rocq's induction engine to handle the temporal state transitions.

### Included Files
- src/FairAllocation.v: The complete functional model and verified proofs.
- _CoqProject: Compilation configuration.
- Makefile: Standard build script (requires Rocq and stdpp).

### Architectural Layers and Results
The project is built on a five-layer inductive stack:

Layer 1: System Environment & Foundations
- single_item_arrival / binary_valuation / constant_valuation: Mathematical properties defining the class of games being verified.
- cumulative_instance / items_up_to: Formal definitions of the temporal "snapshot" used for fairness measurement.
- utility_add / utility_remove: Proves additivity of agent utilities over item sets.

Layer 2: Temporal Evolution & Transitions
- greedy_bundle_step_winner / _loser: Atomic proofs of how agent bundles grow or stay stable during an arrival.
- greedy_bundle_equivalence: Bridges the recursive functional model to the summation of the algorithm's actual outcome.

Layer 3: Greedy Selection Logic
- greedy_utility_guarantee: Verifies that the greedy recipient has the minimum cumulative utility among positive-valuation candidates.
- greedy_utility_monotonic: Verifies that an agent's cumulative utility never decreases over time.

Layer 4: Fairness Invariants (Inductive Engines)
- self_value_invariant: Defines the core inductive property; each agent values their own bundle at least as much as any other agent values it.
- greedy_preserves_ef1 / greedy_preserves_self_value: The primary engines proving that the greedy choice preserves fairness invariants across arrivals.

Layer 5: Master Synthesis
- greedy_is_TEF1: The project's top-level theorem; uses natural number induction to prove that the greedy allocator is Temporal EF1 fair for all time T.

### Deviations from Proposal
While I originally intended to implement the allocator in HeapLang and verify it using Iris separation logic, the complexity of the pure mathematical proof required a strategic shift in scope. To ensure a verified and logically sound submission by the deadline, I prioritized the functional verification in raw Rocq. 

This functional proof serves as the verified "specification" for the algorithm. It handles the hardest part of the project—the game-theoretic logic—and provides the foundational work needed to perform the Iris refinement as part of my ongoing research.

### Conclusion
The resulting proof demonstrates that the greedy online rule is a provably correct allocator for maintaining fairness over time. It utilizes stdpp for set arithmetic and custom tactical automation (v_simpl) to achieve syntactic unification across temporal record projections.
