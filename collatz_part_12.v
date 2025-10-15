Load "collatz_part_11.v".


(* R0R0 Input Lower Bound *)
Lemma R0R0_input_ge_n : forall D n,
  D >= 1 -> n >= 1 ->
  let m := valid_R0R0_entry_number D n in n <= m.
Proof.
  intros D n HD Hn m.
  unfold m, valid_R0R0_entry_number.
  assert (Hpow: 2 ^ D >= 2) by (apply pow2_ge_2; lia).
  assert (Hpow_ge1: 1 <= 2 ^ D) by lia.
  rewrite <- Nat.mul_1_r at 1.
  apply Nat.mul_le_mono_pos_l; lia.
Qed.

(* R0R0 Final Value Exactness *)
Lemma R0R0_output_exact_n : forall D n,
  D >= 1 -> n >= 1 ->
  let m := valid_R0R0_entry_number D n in
  sequence_end m (repeat_R0 D) = n.
Proof.
  intros D n HD Hn m.
  apply repeat_R0_output_reaches_one; lia.
Qed.

(* R0R0 Output Value Bounds *)
Lemma R0R0_output_bounds : forall D n,
  D >= 1 -> n >= 1 ->
  let m := valid_R0R0_entry_number D n in
  1 <= sequence_end m (repeat_R0 D) /\ sequence_end m (repeat_R0 D) <= m.
Proof.
  intros D n HD Hn m.
  split.
  - unfold m. rewrite (R0R0_output_exact_n D n HD Hn). lia.
  - unfold m. rewrite (R0R0_output_exact_n D n HD Hn). apply R0R0_input_ge_n; lia.
Qed.

(* R0R0 Output Minimum Value *)
Lemma R0R0_output_minimal_when_one : forall D,
  D >= 1 ->
  let m := valid_R0R0_entry_number D 1 in
  sequence_end m (repeat_R0 D) = 1.
Proof.
  intros D HD m; apply repeat_R0_output_reaches_one; lia.
Qed.



(* R0R0 Combined Bounds Summary Theorem *)
Theorem R0R0_bounds_summary : forall D n,
  D >= 1 -> n >= 1 ->
  let m := valid_R0R0_entry_number D n in
    1 <= n /\ n <= m /\ sequence_end m (repeat_R0 D) = n.
Proof.
  intros D n HD Hn m; repeat split.
  - lia.
  - apply R0R0_input_ge_n; assumption.
  - apply R0R0_output_exact_n; assumption.
Qed.


(* Combined Bounds General Theorem *)
Theorem build_k_steps_numeric_bounds_exists : forall m,
  m >= 1 ->
  (exists d n, d >= 1 /\ n >= 0 /\
      m = valid_R1R0_entry_number d n /\
      build_k_steps m d = repeat_R1R0 d /\
      2 * 3^d * n <= sequence_end (valid_R1R0_entry_number d n) (repeat_R1R0 d) /\
      3^d - 1 <= sequence_end (valid_R1R0_entry_number d n) (repeat_R1R0 d) /\
      sequence_end (valid_R1R0_entry_number d n) (repeat_R1R0 d) <= 3^d * (2 * n + 1)) \/
  (exists d n, d >= 1 /\ n >= 1 /\
      m = valid_R0R0_entry_number d n /\
      build_k_steps m d = repeat_R0 d /\
      1 <= n /\ n <= m /\
      sequence_end (valid_R0R0_entry_number d n) (repeat_R0 d) = n).
Proof.
  intros m Hm.
  destruct (build_k_steps_pattern_completeness m Hm)
    as [ [d [n [Hd [Hn [Hmdef Hbuild]]]]] | [d [n [Hd [Hn [Hmdef Hbuild]]]]] ].
  - left.
    exists d, n; repeat split; try assumption.
    * apply repeat_R1R0_output_lower_bound_linear; assumption.
    * apply repeat_R1R0_output_lower_bound_const; assumption.
    * apply repeat_R1R0_output_upper_bound; assumption.
  - right.
  pose proof (R0R0_bounds_summary d n Hd Hn) as [Hlow1 [Hlow2 Heq]].
    exists d, n.
    split; [exact Hd |].
    split; [exact Hn |].
    split; [exact Hmdef |].
    split; [exact Hbuild |].
  split; [exact Hlow1 |].
  split; [rewrite Hmdef; exact Hlow2 |].
    exact Heq.
Qed.


(* Comprehensive Bounds Main Theorem *)
Theorem build_k_steps_full_bounds : forall n k,
  valid_input n ->
  k >= 2 ->
  exists ops r0s r1s,
    build_k_steps n k = ops /\
    count_operations ops = (r0s, r1s) /\
    (* Exact R0 count *)
    r0s = k /\
    (* R1 exact expression and bounds *)
    r1s = length ops - k /\
    r1s <= k /\
    r1s <= r0s /\
    (* Total length bilateral bounds *)
    k <= length ops /\ length ops <= 2 * k /\
    (* Sum of counts equals length *)
    r0s + r1s = length ops.
Proof.
  intros n k Hvalid Hk.
  destruct (build_k_steps_structure n k Hvalid Hk) as
    [ops [r0s [r1s [Hops [Hcnt [Hr0 [Hr1_le [Hr1_eq Hlen_le]]]]]]]].
  exists ops, r0s, r1s.
  split; [exact Hops|].
  split; [exact Hcnt|].
  split; [exact Hr0|].
  split; [exact Hr1_eq|].
  split; [exact Hr1_le|].
  split; [rewrite Hr0; exact Hr1_le|].
  pose proof (build_k_steps_length_bound n k Hvalid) as Hlen_bounds.
  rewrite Hops in Hlen_bounds.
  destruct Hlen_bounds as [Hlen_low Hlen_high].
  split; [exact Hlen_low|].
  split; [exact Hlen_le|].
  pose proof (count_sum_c2 ops) as Hsum.
  simpl in Hsum.
  rewrite Hcnt in Hsum.
  exact Hsum.
Qed.