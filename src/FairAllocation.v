From stdpp Require Import prelude fin_sets gmap finite.
Require Import Coq.Logic.FunctionalExtensionality.

(* Online Fair Allocation *)

Section FairAllocation.
  Variable n m T : nat.
  Hypothesis Hn : n > 0.

  Local Notation agent := (fin n).
  Local Notation item := (fin m).
  Local Notation bundle := (gset item).
  Local Notation valuation_function := (agent -> item -> nat).

  (* Types and Records *)

  Definition additive_bundle_val (V : valuation_function) (i : agent) (b : bundle) : nat :=
    set_fold (λ o acc, V i o + acc) 0 b.

  Record static_instance := {
    si_items : gset item;
    si_v : valuation_function;
  }.

  Record allocation (S : gset item) := {
    alloc_map :> agent -> bundle;
    is_disjoint : forall i j, i ≠ j -> alloc_map i ∩ alloc_map j = ∅;
    is_complete : forall o, o ∈ S <-> ∃ i, o ∈ alloc_map i
  }.

  Record temporal_instance := {
    ti_days : fin T -> static_instance;
    ti_disjoint : forall t1 t2 : fin T,
      t1 ≠ t2 -> (ti_days t1).(si_items) ∩ (ti_days t2).(si_items) = ∅;
  }.

  Definition temporal_allocation (inst : temporal_instance) :=
    forall t : fin T, allocation (inst.(ti_days) t).(si_items).

  (* Helper Functions *)

  Definition all_agents : list agent := fin_enum n.

  Definition first_agent : agent.
  Proof.
    destruct n as [|n_prev].
    - exfalso. lia.
    - exact (0%fin : fin (S n_prev)).
  Defined.

  Fixpoint agents_valuing (V : valuation_function) (o : item) (l : list agent) : list agent :=
    match l with
    | [] => []
    | i :: rest => 
        if (0 <? V i o) then i :: (agents_valuing V o rest)
        else agents_valuing V o rest
    end.

  Definition greedy_step_recipient (V : valuation_function) (A : agent -> bundle) (o_set : gset item) : agent :=
    match (elements o_set) with
    | [] => first_agent
    | o :: _ => 
        let candidates := agents_valuing V o all_agents in
        let search_list := if (decide (candidates = [])) then all_agents else candidates in
        match search_list with
        | [] => first_agent 
        | s :: rest => 
            foldr (λ i best, if (additive_bundle_val V i (A i) <? additive_bundle_val V best (A best)) then i else best)
                  s rest
        end
    end.

  Fixpoint greedy_bundle (inst : temporal_instance) (t : nat) (i : agent) : bundle :=
    match t with
    | 0 => ∅
    | S t' =>
        match (decide (t' < T)) with
        | left H => 
            let A_prev := greedy_bundle inst t' in
            let day := inst.(ti_days) (nat_to_fin H) in
            let winner := greedy_step_recipient day.(si_v) A_prev day.(si_items) in
            if (decide (i = winner)) then A_prev i ∪ day.(si_items) else A_prev i
        | right _ => greedy_bundle inst t' i
        end
    end.

  Fixpoint cumulative_bundle (inst : temporal_instance) (A : temporal_allocation inst) (t : nat) (i : agent) : bundle :=
    match t with
    | 0 => ∅
    | S t' =>
        match (decide (t' < T)) with
        | left H => cumulative_bundle inst A t' i ∪ (A (nat_to_fin H)) i
        | right _ => cumulative_bundle inst A t' i
        end
    end.

  Fixpoint items_up_to (inst : temporal_instance) (t : nat) : gset item :=
    match t with
    | 0 => ∅
    | S t' =>
        match (decide (t' < T)) with
        | left H => items_up_to inst t' ∪ (inst.(ti_days) (nat_to_fin H)).(si_items)
        | right _ => items_up_to inst t'
        end
    end.

  Definition cumulative_instance (inst : temporal_instance) (t : fin T) : static_instance := {|
    si_items := items_up_to inst (S (fin_to_nat t));
    si_v := (inst.(ti_days) t).(si_v);
  |}.

  (* Problem Constraints *)

  Definition single_item_arrival (inst : temporal_instance) : Prop :=
    forall t : fin T, size (inst.(ti_days) t).(si_items) = 1.

  Definition binary_valuation (inst : temporal_instance) : Prop :=
    forall t i o, (inst.(ti_days) t).(si_v) i o = 0 \/ (inst.(ti_days) t).(si_v) i o = 1.

  Definition constant_valuation (inst : temporal_instance) : Prop :=
    forall t1 t2 i o, (inst.(ti_days) t1).(si_v) i o = (inst.(ti_days) t2).(si_v) i o.

  (* Fairness Definitions *)

  Definition EF (inst : static_instance) (A : agent -> bundle) : Prop :=
    forall i j, additive_bundle_val inst.(si_v) i (A i) >= additive_bundle_val inst.(si_v) i (A j).

  Definition EF1 (inst : static_instance) (A : agent -> bundle) : Prop :=
    forall i j, (additive_bundle_val inst.(si_v) i (A i) >= additive_bundle_val inst.(si_v) i (A j)) \/ 
      exists g, g ∈ A j /\ 
        additive_bundle_val inst.(si_v) i (A i) >= additive_bundle_val inst.(si_v) i (A j ∖ {[g]}).

  Definition TEF1 (inst : temporal_instance) (A : temporal_allocation inst) : Prop :=
    forall t : fin T, EF1 (cumulative_instance inst t) (cumulative_bundle inst A (S (fin_to_nat t))).

  (* Greedy Algorithm *)

  Definition greedy_allocator (inst : temporal_instance) : temporal_allocation inst.
  Proof.
    refine (λ t, {|
      alloc_map := λ i, 
        let A_prev := greedy_bundle inst (fin_to_nat t) in
        let day := (inst.(ti_days) t) in
        let winner := greedy_step_recipient day.(si_v) A_prev day.(si_items) in
        if (decide (i = winner)) then day.(si_items) else ∅;
      is_disjoint := _;
      is_complete := _
    |}).
    - intros i j Hij. simpl. case_decide; case_decide; set_solver.
    - intros o. simpl. split.
      + intros Ho.
        set (winner := greedy_step_recipient _ _ _).
        exists winner. case_decide; [done | contradiction].
      + intros [i Hi].
        case_decide; [subst; done | set_solver].
  Defined.

  (* Utility and Bundle Arithmetic *)

  Lemma utility_empty (V : valuation_function) (i : agent) :
    additive_bundle_val V i ∅ = 0.
  Proof.
    unfold additive_bundle_val. apply set_fold_empty.
  Qed.

  Lemma utility_singleton (V : valuation_function) (i : agent) (o : item) :
    additive_bundle_val V i {[ o ]} = V i o.
  Proof.
    unfold additive_bundle_val. rewrite set_fold_singleton. lia.
  Qed.

  Lemma utility_add (V : valuation_function) (i : agent) (b : bundle) (o : item) :
    o ∉ b -> additive_bundle_val V i ({[ o ]} ∪ b) = V i o + additive_bundle_val V i b.
  Proof.
    intros Ho. unfold additive_bundle_val, set_fold. simpl.
    assert (elements ({[o]} ∪ b) ≡ₚ o :: elements b) as Hperm.
    { apply elements_union_singleton. done. }
    assert (foldr (λ o0 acc, V i o0 + acc) 0 (elements ({[o]} ∪ b)) =
            foldr (λ o0 acc, V i o0 + acc) 0 (o :: elements b)) as Hfold.
    { apply foldr_permutation_proper.
      - apply _.
      - intros x. apply _.
      - intros x y z. lia.
      - done.
    }
    rewrite Hfold. simpl. lia.
  Qed.

  Lemma utility_remove (V : valuation_function) (i : agent) (b : bundle) (o : item) :
    o ∈ b -> additive_bundle_val V i (b ∖ {[ o ]}) = additive_bundle_val V i b - V i o.
  Proof.
    intros Ho.
    assert (b = ({[o]} : bundle) ∪ (b ∖ ({[o]} : bundle))) as Hb.
    { apply union_difference_singleton_L. done. }
    rewrite Hb at 2.
    rewrite utility_add; [| set_solver].
    lia.
  Qed.

  Lemma ef1_neutral_preservation (V : valuation_function) (i : agent) (A B : bundle) (o g : item) :
    V i o = 0 ->
    g ≠ o ->
    o ∉ B ->
    g ∈ B ->
    additive_bundle_val V i A >= additive_bundle_val V i (B ∖ {[ g ]}) ->
    additive_bundle_val V i A >= additive_bundle_val V i ((B ∪ {[ o ]}) ∖ {[ g ]}).
  Proof.
    intros Hvo Hgo Ho_notin Hg_in Hef1_old.
    assert (Hset : (B ∪ {[ o ]}) ∖ {[ g ]} = {[ o ]} ∪ (B ∖ {[ g ]})) by (apply leibniz_equiv; set_solver).
    rewrite Hset.
    rewrite utility_add.
    - lia.
    - set_solver.
  Qed.

  Lemma utility_extensionality (V1 V2 : valuation_function) (i : agent) (b : bundle) :
    (forall o, V1 i o = V2 i o) ->
    additive_bundle_val V1 i b = additive_bundle_val V2 i b.
  Proof.
    intros Hval.
    induction b as [| o b Hnotin IH] using set_ind_L.
    - rewrite utility_empty.
      rewrite utility_empty.
      reflexivity.
    - rewrite utility_add.
      2: exact Hnotin.
      rewrite utility_add.
      2: exact Hnotin.
      rewrite Hval.
      rewrite IH.
      reflexivity.
  Qed.

  Lemma utility_invariance (inst : temporal_instance) :
    constant_valuation inst ->
    forall t1 t2 i b, additive_bundle_val (inst.(ti_days) t1).(si_v) i b =
                     additive_bundle_val (inst.(ti_days) t2).(si_v) i b.
  Proof.
    intros Hconst t1 t2 i b.
    apply utility_extensionality.
    intros o.
    apply Hconst.
  Qed.

  Lemma cumulative_instance_v_eq (inst : temporal_instance) (t : fin T) :
    (cumulative_instance inst t).(si_v) = (inst.(ti_days) t).(si_v).
  Proof. reflexivity. Qed.

  Lemma utility_harmony (inst : temporal_instance) (t1 t2 : fin T) (i : agent) (b : bundle) :
    constant_valuation inst ->
    additive_bundle_val (si_v (cumulative_instance inst t1)) i b = 
    additive_bundle_val (si_v (ti_days inst t2)) i b.
  Proof.
    intros Hconst.
    rewrite cumulative_instance_v_eq.
    apply utility_invariance.
    exact Hconst.
  Qed.

  (* Proof Automation *)

  Ltac v_simpl inst Hconst :=
    repeat match goal with
    | |- context [ si_v (cumulative_instance _ ?time) ] =>
        rewrite (cumulative_instance_v_eq inst time)
    | H: context [ si_v (cumulative_instance _ ?time) ] |- _ =>
        rewrite (cumulative_instance_v_eq inst time) in H
    | |- context [ additive_bundle_val (si_v (ti_days _ ?t1)) ?i ?b ] =>
        rewrite (utility_invariance inst Hconst t1 _)
    | H: context [ additive_bundle_val (si_v (ti_days _ ?t1)) ?i ?b ] |- _ =>
        rewrite (utility_invariance inst Hconst t1 _) in H
    end.


  Ltac simplify_bundles :=
    repeat match goal with
    | |- context [ (?A ∪ {[?o]}) ∖ {[?o]} ] => 
        replace ((A ∪ {[o]}) ∖ {[o]}) with A by (apply leibniz_equiv; set_solver)
    | |- context [ ({[?o]} ∪ ?A) ∖ {[?o]} ] => 
        replace (({[o]} ∪ A) ∖ {[o]}) with A by (apply leibniz_equiv; set_solver)
    | |- context [ ?A ∪ {[?o]} ] =>
        replace (A ∪ {[o]}) with ({[o]} ∪ A) by (apply leibniz_equiv; set_solver)
    end.

  (* Allocation State Lemmas *)

  Lemma greedy_bundle_equivalence (inst : temporal_instance) (t : nat) (i : agent) :
    greedy_bundle inst t i = cumulative_bundle inst (greedy_allocator inst) t i.
  Proof.
    induction t as [| t' IH].
    - reflexivity.
    - simpl. case_decide as Hlt; [| exact IH].
      rewrite IH. simpl.
      rewrite fin_to_nat_to_fin.
      repeat case_decide; set_solver.
  Qed.

  Lemma greedy_bundle_zero (inst : temporal_instance) (i : agent) :
    greedy_bundle inst 0 i = ∅.
  Proof. done. Qed.

  Lemma greedy_bundle_step_winner (inst : temporal_instance) (t : fin T) (i : agent) :
    let A_prev := greedy_bundle inst (fin_to_nat t) in
    let day := inst.(ti_days) t in
    i = greedy_step_recipient day.(si_v) A_prev day.(si_items) ->
    greedy_bundle inst (S (fin_to_nat t)) i = A_prev i ∪ day.(si_items).
  Proof.
    intros A_prev day Hwinner. simpl.
    case_decide as Hlt.
    - rewrite nat_to_fin_to_nat. subst A_prev day. simpl in Hwinner.
      case_decide; [done | contradiction].
    - pose proof (fin_to_nat_lt t). lia.
  Qed.

  Lemma greedy_bundle_step_loser (inst : temporal_instance) (t : fin T) (i : agent) :
    let A_prev := greedy_bundle inst (fin_to_nat t) in
    let day := inst.(ti_days) t in
    i ≠ greedy_step_recipient day.(si_v) A_prev day.(si_items) ->
    greedy_bundle inst (S (fin_to_nat t)) i = A_prev i.
  Proof.
    intros A_prev day Hloser. simpl.
    case_decide as Hlt.
    - rewrite nat_to_fin_to_nat. subst A_prev day. simpl in Hloser.
      case_decide; [contradiction | done].
    - pose proof (fin_to_nat_lt t). lia.
  Qed.

  (* Utility Properties *)

  Lemma item_not_in_prev_bundle (inst : temporal_instance) (t : fin T) (i : agent) (o : item) :
    let day := inst.(ti_days) t in
    let A_prev := greedy_bundle inst (fin_to_nat t) in
    o ∈ day.(si_items) ->
    o ∉ A_prev i.
  Proof.
    intros day A_prev Ho. unfold A_prev.
    assert (forall n0, n0 <= fin_to_nat t -> o ∉ greedy_bundle inst n0 i) as H_ind.
    {
      induction n0 as [|n0 IHn0].
      - intros _. rewrite greedy_bundle_zero. set_solver.
      - intros Hlt.
        assert (Hlt_prev : n0 <= fin_to_nat t) by lia.
        pose proof (IHn0 Hlt_prev) as Hnotin_prev.
        simpl. case_decide as H_n0_T; [| done].
        case_decide as H_winner; [| done].
        assert (t ≠ nat_to_fin H_n0_T).
        { intros H_eq. apply (f_equal (@fin_to_nat T)) in H_eq. 
          rewrite fin_to_nat_to_fin in H_eq. lia. }
        pose proof (inst.(ti_disjoint) t (nat_to_fin H_n0_T) H) as H_disj.
        set_solver.
    }
    apply H_ind. lia.
  Qed.

  Lemma greedy_utility_monotonic (inst : temporal_instance) (t : fin T) (i : agent) :
    single_item_arrival inst ->
    binary_valuation inst ->
    additive_bundle_val (inst.(ti_days) t).(si_v) i (greedy_bundle inst (S (fin_to_nat t)) i) >=
    additive_bundle_val (inst.(ti_days) t).(si_v) i (greedy_bundle inst (fin_to_nat t) i).
  Proof.
    intros Hsingle Hbin.
    destruct (size_1_elem_of (si_items (ti_days inst t))) as [o Ho_set].
    { apply Hsingle. }
    apply leibniz_equiv in Ho_set.
    set (winner := greedy_step_recipient (si_v (ti_days inst t)) (greedy_bundle inst (fin_to_nat t)) {[o]}).
    destruct (decide (i = winner)) as [Hi_win | Hi_lose].
    - subst i.
      rewrite greedy_bundle_step_winner.
      + rewrite Ho_set.
        assert (Hunion : greedy_bundle inst t winner ∪ {[o]} = {[o]} ∪ greedy_bundle inst t winner).
        { apply leibniz_equiv. set_solver. }
        rewrite Hunion.
        rewrite (utility_add _ winner _ o).
        * lia.
        * apply item_not_in_prev_bundle. 
          rewrite Ho_set. 
          set_solver.
      + rewrite Ho_set.
        reflexivity.
    - rewrite greedy_bundle_step_loser.
      + lia.
      + subst winner. rewrite Ho_set. exact Hi_lose.
  Qed.

  (* Greedy Rule Properties *)

  Lemma agent_in_candidates (V : valuation_function) (o : item) (i : agent) (l : list agent) :
    i ∈ l ->
    V i o > 0 ->
    i ∈ agents_valuing V o l.
  Proof.
    intros Hin Hval.
    induction l as [|x l' IH].
    - apply not_elem_of_nil in Hin. contradiction.
    - simpl. apply elem_of_cons in Hin as [-> | Hin].
      + destruct (0 <? V x o) eqn:Hcmp.
        * set_solver.
        * apply Nat.ltb_lt in Hval. congruence.
      + pose proof (IH Hin) as H_in_filter.
        destruct (0 <? V x o) eqn:Hcmp.
        * set_solver.
        * exact H_in_filter.
  Qed.

  Lemma greedy_recipient_in_list (V : valuation_function) (A : agent -> bundle) (l : list agent) (s : agent) :
    foldr (λ i best, if (additive_bundle_val V i (A i) <? additive_bundle_val V best (A best)) then i else best) s l ∈ s :: l.
  Proof.
    induction l as [|x l' IH].
    - simpl. set_solver.
    - simpl. destruct (additive_bundle_val V x (A x) <? additive_bundle_val V _ (A _)) eqn:Hcmp.
      + set_solver.
      + pose proof IH. set_solver.
  Qed.

  Lemma agents_valuing_proper (V : valuation_function) (o : item) (l : list agent) (i : agent) :
    i ∈ agents_valuing V o l -> V i o > 0.
  Proof.
    induction l as [|x l' IH].
    - simpl. set_solver.
    - simpl. destruct (0 <? V x o) eqn:Hcmp.
      + intros Hi. apply elem_of_cons in Hi as [-> | Hi].
        * apply Nat.ltb_lt in Hcmp. lia.
        * exact (IH Hi).
      + intros Hi. exact (IH Hi).
  Qed.

  Lemma greedy_winner_values_item (V : valuation_function) (A : agent -> bundle) (o : item) :
    (exists j, V j o > 0) ->
    V (greedy_step_recipient V A {[ o ]}) o > 0.
  Proof.
    intros [j Hval].
    unfold greedy_step_recipient.
    simpl. 
    set (candidates := agents_valuing V o all_agents).
    assert (H_not_empty : candidates ≠ []).
    { intros H_empty.
      pose proof (agent_in_candidates V o j all_agents (elem_of_enum j) Hval) as H_in.
      unfold candidates in H_empty. rewrite H_empty in H_in. set_solver.
    }
    destruct (decide (candidates = [])); [contradiction |].
    destruct candidates as [|s rest] eqn:H_sl_new.
    { contradiction. }
    rewrite elements_singleton. simpl.
    fold candidates. rewrite -> H_sl_new. 
    destruct (decide (s :: rest = [])); [contradiction |].
    pose proof (greedy_recipient_in_list V A rest s) as H_winner_in.
    apply (agents_valuing_proper V o all_agents).
    unfold candidates in H_sl_new. rewrite H_sl_new. exact H_winner_in.
  Qed.

  Lemma greedy_winner_is_minimum (V : valuation_function) (A : agent -> bundle) (l : list agent) (s : agent) (j : agent) :
    j ∈ s :: l ->
    let winner := foldr (λ i best, if (additive_bundle_val V i (A i) <? additive_bundle_val V best (A best)) then i else best) s l in
    additive_bundle_val V winner (A winner) <= additive_bundle_val V j (A j).
  Proof.
    revert j.
    induction l as [|x l' IH]; intros j Hj winner; simpl in winner.
    - subst winner.
      apply elem_of_cons in Hj as [-> | Hj]; [lia |].
      apply not_elem_of_nil in Hj. contradiction.
    - set (f := λ i best, if additive_bundle_val V i (A i) <? additive_bundle_val V best (A best) then i else best) in *.
      set (w_prev := foldr f s l') in *.
      destruct (additive_bundle_val V x (A x) <? additive_bundle_val V w_prev (A w_prev)) eqn:Hcmp.
      + subst winner.
        apply Nat.ltb_lt in Hcmp.
        apply elem_of_cons in Hj as [-> | Hj].
        * assert (Hs : s ∈ s :: l') by set_solver.
          specialize (IH s Hs). simpl in IH. lia.
        * apply elem_of_cons in Hj as [-> | Hj]; [lia |].
          assert (Hjl : j ∈ s :: l') by set_solver.
          specialize (IH j Hjl). simpl in IH. lia.
      + subst winner.
        apply Nat.ltb_ge in Hcmp.
        apply elem_of_cons in Hj as [-> | Hj].
        * assert (Hs : s ∈ s :: l') by set_solver.
          specialize (IH s Hs). simpl in IH. lia.
        * apply elem_of_cons in Hj as [-> | Hj].
          { done. }
          specialize (IH j).
          simpl in IH. 
          apply IH.
          set_solver.
  Qed.

  Lemma greedy_utility_guarantee (V : valuation_function) (A : agent -> bundle) (o : item) (i winner : agent) :
    winner = greedy_step_recipient V A {[ o ]} ->
    V i o > 0 ->
    additive_bundle_val V winner (A winner) <= additive_bundle_val V i (A i).
  Proof.
    intros Hwinner Hval.
    unfold greedy_step_recipient in Hwinner.
    rewrite elements_singleton in Hwinner.
    simpl in Hwinner.
    set (candidates := agents_valuing V o all_agents) in *.
    assert (Hi : i ∈ candidates).
    { apply agent_in_candidates.
      - change all_agents with (enum agent).
        apply elem_of_enum.
      - exact Hval. }
    destruct candidates as [|s rest] eqn:Heq; [set_solver |].
    rewrite Hwinner.
    apply greedy_winner_is_minimum.
    exact Hi.
  Qed.

  (* Fairness Preservation Invariants *)

  Definition self_value_invariant (V : valuation_function) (A : agent -> bundle) : Prop :=
    forall i j, additive_bundle_val V i (A i) >= additive_bundle_val V j (A i).

  Lemma self_value_invariant_empty (V : valuation_function) :
    self_value_invariant V (λ _, ∅).
  Proof.
    intros i j.
    rewrite ! utility_empty.
    lia.
  Qed.

  Lemma ef1_empty (inst : static_instance) :
    EF1 inst (λ _, ∅).
  Proof.
    intros i j.
    left.
    rewrite ! utility_empty.
    lia.
  Qed.

  Lemma greedy_preserves_self_value (inst : temporal_instance) (t : fin T) :
    single_item_arrival inst ->
    binary_valuation inst ->
    constant_valuation inst ->
    self_value_invariant (inst.(ti_days) t).(si_v) (greedy_bundle inst (fin_to_nat t)) ->
    forall (Ht_next : fin_to_nat t < T),
    self_value_invariant (inst.(ti_days) (nat_to_fin Ht_next)).(si_v) (greedy_bundle inst (S (fin_to_nat t))).
  Proof.
    intros Hsingle Hbin Hconst Hinv Ht_next i j.
    set (t_now := nat_to_fin Ht_next).
    assert (Hidx : t_now = t).
    { apply fin_to_nat_inj. unfold t_now. rewrite fin_to_nat_to_fin. reflexivity. }
    rewrite <- Hidx in *.
    pose proof (Hsingle t_now) as Hsz.
    destruct (size_1_elem_of (si_items (ti_days inst t_now))) as [o Ho_set].
    { exact Hsz. }
    apply leibniz_equiv in Ho_set.
    rewrite Ho_set in *.
    remember (greedy_step_recipient (si_v (ti_days inst t_now)) (greedy_bundle inst (fin_to_nat t_now)) {[o]}) as winner eqn:Hwinner.
    destruct (decide (i = winner)) as [Hi_win | Hi_lose].
    - subst i.
      assert (Hbundle : greedy_bundle inst (S (fin_to_nat t_now)) winner = greedy_bundle inst (fin_to_nat t_now) winner ∪ {[o]}).
      { rewrite (greedy_bundle_step_winner _ t_now).
        - rewrite Ho_set. reflexivity.
        - rewrite Hwinner. rewrite Ho_set. reflexivity. }
      rewrite Hbundle.
      assert (Hnot_in : o ∉ greedy_bundle inst (fin_to_nat t_now) winner).
      { apply item_not_in_prev_bundle. rewrite Ho_set. set_solver. }
      simplify_bundles.
      rewrite (utility_add _ winner _ o); [| exact Hnot_in].
      rewrite (utility_add _ j _ o); [| exact Hnot_in].
      assert (Hinv_now : additive_bundle_val (si_v (ti_days inst t_now)) winner (greedy_bundle inst (fin_to_nat t_now) winner) >= 
                        additive_bundle_val (si_v (ti_days inst t_now)) j (greedy_bundle inst (fin_to_nat t_now) winner)).
      { v_simpl inst Hconst. apply Hinv. }
      assert (Hvo : si_v (ti_days inst t_now) winner o >= si_v (ti_days inst t_now) j o).
      { destruct (Hbin t_now j o) as [Hj0 | Hj1].
        - rewrite Hj0. lia.
        - assert (Hex : exists k, si_v (ti_days inst t_now) k o > 0) by (exists j; lia).
          assert (Hw_val : si_v (ti_days inst t_now) winner o > 0).
          { rewrite Hwinner. apply greedy_winner_values_item. exact Hex. }
          destruct (Hbin t_now winner o); lia. }
      lia.
    - assert (Hbundle_i : greedy_bundle inst (S (fin_to_nat t_now)) i = greedy_bundle inst (fin_to_nat t_now) i).
      { rewrite (greedy_bundle_step_loser _ t_now).
        - reflexivity.
        - rewrite Ho_set. rewrite <- Hwinner. exact Hi_lose. }
      rewrite Hbundle_i. v_simpl inst Hconst. apply Hinv.
  Qed.

  Lemma greedy_preserves_ef1 (inst : temporal_instance) (t : fin T) :
    single_item_arrival inst ->
    binary_valuation inst ->
    constant_valuation inst ->
    EF1 (cumulative_instance inst t) (greedy_bundle inst (fin_to_nat t)) ->
    self_value_invariant (inst.(ti_days) t).(si_v) (greedy_bundle inst (fin_to_nat t)) ->
    forall (Ht_next : fin_to_nat t < T),
    EF1 (cumulative_instance inst (nat_to_fin Ht_next)) (greedy_bundle inst (S (fin_to_nat t))).
  Proof.
    intros Hsingle Hbin Hconst Hef1 Hinv Ht_next i j.
    set (t_now := nat_to_fin Ht_next).
    assert (Hidx : t_now = t).
    { apply fin_to_nat_inj. unfold t_now. rewrite fin_to_nat_to_fin. reflexivity. }
    rewrite <- Hidx in *.
    destruct (size_1_elem_of (si_items (ti_days inst t_now))) as [o Ho_set].
    { apply Hsingle. }
    apply leibniz_equiv in Ho_set.
    remember (greedy_step_recipient (si_v (ti_days inst t_now)) (greedy_bundle inst (fin_to_nat t_now)) {[o]}) as winner eqn:Hwinner.
    destruct (decide (j = winner)) as [Hj_win | Hj_lose].
    - subst j.
      destruct (decide (i = winner)) as [Hi_win | Hi_lose].
      + subst i. left. lia.
      + assert (Hbundle_i : greedy_bundle inst (S (fin_to_nat t_now)) i = greedy_bundle inst (fin_to_nat t_now) i).
        { rewrite (greedy_bundle_step_loser _ t_now).
          - reflexivity.
          - rewrite Ho_set. subst winner. exact Hi_lose. }
        assert (Hwinner_alloc : greedy_bundle inst (S (fin_to_nat t_now)) winner = greedy_bundle inst (fin_to_nat t_now) winner ∪ {[o]}).
        { rewrite (greedy_bundle_step_winner _ t_now).
          - rewrite Ho_set. reflexivity.
          - rewrite Hwinner. rewrite Ho_set. reflexivity. }
        assert (Hnot_in_winner : o ∉ greedy_bundle inst (fin_to_nat t_now) winner).
        { apply item_not_in_prev_bundle. set_solver. }
        destruct (Hbin t_now i o) as [Hi0 | Hi1].
        * pose proof (Hef1 i winner) as Hef_yesterday.
          destruct Hef_yesterday as [Hef | [g [Hg_in Hef_g]]].
          -- left. unfold EF in *. v_simpl inst Hconst.
             rewrite Hwinner_alloc, Hbundle_i. simplify_bundles.
             rewrite (utility_add _ i _ o); [| exact Hnot_in_winner].
             rewrite Hi0. lia.
          -- right. exists g. split.
             ++ rewrite Hwinner_alloc. set_solver.
             ++ rewrite Hwinner_alloc, Hbundle_i.
                apply ef1_neutral_preservation; [rewrite cumulative_instance_v_eq; exact Hi0 | | exact Hnot_in_winner | exact Hg_in |].
                ** intros ->. contradiction (Hnot_in_winner Hg_in).
                ** v_simpl inst Hconst. exact Hef_g.
        * right. exists o. split.
          -- rewrite Hwinner_alloc. set_solver.
          -- rewrite Hwinner_alloc, Hbundle_i. simplify_bundles.
             assert (Hi_pos : si_v (ti_days inst t_now) i o > 0) by lia.
             pose proof (greedy_utility_guarantee (si_v (ti_days inst t_now)) (greedy_bundle inst (fin_to_nat t_now)) o i winner Hwinner Hi_pos) as Hgreedy.
             pose proof (Hinv winner i) as Hself.
             v_simpl inst Hconst. lia.
    - assert (Hbundle_j : greedy_bundle inst (S (fin_to_nat t_now)) j = greedy_bundle inst (fin_to_nat t_now) j).
      { rewrite (greedy_bundle_step_loser _ t_now).
        - reflexivity.
        - rewrite Ho_set. rewrite <- Hwinner. exact Hj_lose. }
      pose proof (greedy_utility_monotonic inst t_now i Hsingle Hbin) as Hmono.
      pose proof (Hef1 i j) as Hef_yesterday.
      destruct Hef_yesterday as [Hef | [g [Hg_in Hef_g]]].
      + left. rewrite Hbundle_j. v_simpl inst Hconst. 
        lia.
      + right. exists g. split.
        * rewrite Hbundle_j. exact Hg_in.
        * rewrite Hbundle_j. v_simpl inst Hconst. 
          lia.
  Qed.

  Theorem greedy_is_TEF1 (inst : temporal_instance) :
    single_item_arrival inst ->
    binary_valuation inst ->
    constant_valuation inst ->
    TEF1 inst (greedy_allocator inst).
  Proof.
    intros Hsingle Hbin Hconst.
    unfold TEF1. intros t.
    assert (H_all : forall k, k <= T -> 
      (forall day : fin T, self_value_invariant (si_v (ti_days inst day)) (greedy_bundle inst k)) /\
      (forall day : fin T, EF1 {| si_items := items_up_to inst k; si_v := si_v (ti_days inst day) |} (greedy_bundle inst k))).
    {
      induction k as [| k' IH].
      - intros _. split; intros d.
        + apply self_value_invariant_empty.
        + apply ef1_empty.
      - intros HkS.
        assert (Hk' : k' <= T) by lia.
        destruct (IH Hk') as [Hinv_prev Hef1_prev].
        assert (Hlt : k' < T) by lia.
        set (tk := nat_to_fin Hlt).
        assert (H_align : fin_to_nat tk = k').
        { unfold tk. rewrite fin_to_nat_to_fin. reflexivity. }
        rewrite <- H_align in *.
        split; intros d i j.
        + (* Self-Value Preservation *)
          pose proof (greedy_preserves_self_value inst tk Hsingle Hbin Hconst (Hinv_prev tk) HkS i j) as Hpres.
          setoid_rewrite (utility_invariance inst Hconst d (nat_to_fin HkS)).
          exact Hpres.
        + (* EF1 Preservation *)
          pose proof (greedy_preserves_ef1 inst tk Hsingle Hbin Hconst (Hef1_prev tk) (Hinv_prev tk) HkS i j) as Hpres.
          setoid_rewrite (utility_invariance inst Hconst d (nat_to_fin HkS)).
          exact Hpres.
    }
    assert (Hbound : S (fin_to_nat t) <= T) by (pose proof (fin_to_nat_lt t); lia).
    destruct (H_all (S (fin_to_nat t)) Hbound) as [_ Hef1].
    specialize (Hef1 t).
    v_simpl inst Hconst.
    unfold EF1 in *.
    setoid_rewrite <- greedy_bundle_equivalence.
    exact Hef1.
  Qed.

End FairAllocation.
