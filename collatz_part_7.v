Load "collatz_part_6.v".


(* Lemma about single-step R1R0 operation *)
Lemma R1R0_single_step : forall n i,
  valid_input n ->
  is_odd (nth_sequence_value n i) ->
  exists k, nth_sequence_value n (i + 2) = 3*k + 2.
Proof.
intros n i Hvalid Hodd.
remember (nth_sequence_value n i) as input_val eqn:Heq_input.
destruct (odd_decomposition input_val Hodd) as [m Hm].
exists m.
assert (H_mid: nth_sequence_value n (i + 1) = 3 * input_val + 1).
{
replace (i + 1) with (S i) by lia.
rewrite nth_sequence_value_succ.
unfold collatz_step.
rewrite <- Heq_input.
unfold is_odd in Hodd.
rewrite Hodd.
reflexivity.
}
assert (H_mid_even: is_even (nth_sequence_value n (i + 1))).
{
rewrite H_mid.
apply even_3n_plus_1.
exact Hodd.
}
replace (i + 2) with (S (i + 1)) by lia.
rewrite nth_sequence_value_succ.
unfold collatz_step.
rewrite H_mid.
assert (H_even_3n1: Nat.even (3 * input_val + 1) = true).
{
rewrite <- H_mid.
unfold is_even in H_mid_even.
exact H_mid_even.
}
rewrite H_even_3n1.
rewrite Hm.
assert (H_check1: 3 * (2 * m + 1) = 6 * m + 3) by ring.
assert (H_check2: 3 * (2 * m + 1) + 1 = 6 * m + 4) by ring.
assert (H_check3: (2 * 3 * m + 4) / 2 = 3 * m + 2).
{
assert (H_ge_1: 3 * m + 2 >= 1) by lia.
replace (2 * 3 * m + 4) with (2 * (3 * m + 2)) by ring.
apply even_div2_mul2.
exact H_ge_1.
}
replace (3 * (2 * m + 1) + 1) with (6 * m + 4) by ring.
exact H_check3.
Qed.



(* When the sequence starts with R0, consecutive R1R0 count and R1 count remain unchanged *)
Lemma congruent_R0_prefix: forall t2,
  count_consecutive_R1R0 (R0 :: t2) = count_consecutive_R1R0 t2 /\
  count_R1 (R0 :: t2) = count_R1 t2.
Proof.
intros t2.
destruct t2 as [| h t2'].
-
simpl. split; reflexivity.
- destruct t2' as [| h2 t2''].
+
simpl. split; reflexivity.
+
simpl. split; reflexivity.
Qed.




(* Connection property of nth_sequence_value *)
Lemma nth_sequence_value_app : forall n k1 k2,
  nth_sequence_value n (k1 + k2) = nth_sequence_value (nth_sequence_value n k1) k2.
Proof.
intros n k1 k2.
induction k2 as [|k2' IH].
-
simpl. rewrite Nat.add_0_r. reflexivity.
-
rewrite Nat.add_succ_r. simpl. rewrite IH. reflexivity.
Qed.

(* Connection property of sequence end value *)
Lemma sequence_end_app : forall n ops1 ops2,
  sequence_end n (ops1 ++ ops2) = sequence_end (sequence_end n ops1) ops2.
Proof.
intros n ops1 ops2.
unfold sequence_end.
rewrite app_length.
rewrite nth_sequence_value_app.
reflexivity.
Qed.

