Load "collatz_part_2.v".


(* Basic properties of R1R0 entry number: >=1 and odd *)
Lemma valid_R1R0_entry_number_properties : forall d n,
  d >= 1 -> n >= 0 ->
  let m := valid_R1R0_entry_number d n in
  m >= 1 /\ is_odd m.
Proof.
intros d n Hd Hn.
unfold valid_R1R0_entry_number.
split.
-
assert (H_pow_ge2: 2^d >= 2) by (apply pow2_ge_2; exact Hd).
assert (H_pow_ge1: 2^d - 1 >= 1) by lia.
lia.
-
unfold is_odd.
rewrite Nat.even_add.
assert (H_even_part: Nat.even (2 * 2^d * n) = true).
{
assert (H_rewrite: 2 * 2^d * n = 2 * (2^d * n)) by ring.
rewrite H_rewrite.
apply Nat.even_mul.
}
rewrite H_even_part.
simpl.
assert (H_odd_part: Nat.even (2^d - 1) = false).
{
apply pow2_minus_1_odd.
exact Hd.
}
rewrite H_odd_part.
simpl.
reflexivity.
Qed.

(* Basic properties of R0R0 entry number: >=2 and even *)
Lemma valid_R0R0_entry_number_properties : forall d n,
  d >= 1 -> n >= 1 ->
  let m := valid_R0R0_entry_number d n in
  m >= 2 /\ is_even m.
Proof.
intros d n Hd Hn m. unfold m, valid_R0R0_entry_number.
split.
-
assert (H2d: 2^d >= 2) by (apply pow2_ge_2; exact Hd).
assert (Hmul: 1 <= n) by exact Hn.
assert (Hineq: 1 * 2^d <= n * 2^d).
{ apply Nat.mul_le_mono_r. exact Hmul. }
rewrite Nat.mul_1_l in Hineq.
lia.
-
destruct d as [|d'].
+ lia.
+ unfold is_even.
assert (H_fact: 2^(S d') = 2 * 2^d') by reflexivity.
rewrite H_fact.
rewrite Nat.mul_comm with (n := n).
rewrite <- Nat.mul_assoc.
rewrite Nat.even_mul.
simpl. reflexivity.
Qed.

(* Any odd number greater than 1 can be uniquely expressed as an R1R0 entry number *)
Lemma odd_eq_R1R0_entry_number :
  forall m, m >= 1 -> is_odd m ->
    exists d n, d >= 1 /\ n >= 0 /\
      m = valid_R1R0_entry_number d n.
Proof.
intros m Hm1 Hodd.
assert (H_even: is_even (m + 1)).
{
unfold is_even.
rewrite Nat.even_add.
rewrite Hodd.
simpl.
reflexivity.
}
assert (H_ge2: m + 1 >= 2) by lia.
apply power2_odd_decomposition in H_even as [d [q [Hd [Hq [Hm1_eq Hqodd]]]]]; auto.
apply odd_decomposition in Hqodd as [n Hqn].
exists d, n.
repeat split; try lia.
unfold valid_R1R0_entry_number.
assert (H_expand: m + 1 = 2^d * (2 * n + 1)).
{
rewrite <- Hqn.
exact Hm1_eq.
}
assert (H_mult: 2^d * (2 * n + 1) = 2^d * 2 * n + 2^d).
{
ring.
}
assert (H_comm: 2^d * 2 * n = 2 * 2^d * n).
{
ring.
}
rewrite H_mult, H_comm in H_expand.
assert (H_pow_ge2: 2^d >= 2).
{
apply pow2_ge_2.
exact Hd.
}
lia.
Qed.

(* Any even number greater than 1 can be uniquely expressed as an R0R0 entry number *)
Lemma even_eq_R0R0_entry_number :
  forall m, m >= 1 -> is_even m ->
    exists d n, d >= 1 /\ n >= 1 /\
      m = valid_R0R0_entry_number d n.
Proof.
intros m Hm1 Heven.
apply even_decomposition in Heven as [k Hk].
assert (Hk_ge1: k >= 1).
{
destruct k as [| k'].
-
rewrite Hk in Hm1.
simpl in Hm1.
lia.
-
lia.
}
exists 1, k.
repeat split.
-
lia.
-
exact Hk_ge1.
-
unfold valid_R0R0_entry_number.
simpl.
rewrite Hk.
ring.
Qed.



(* Complete classification of positive integers: odd numbers as R1R0 entries, even numbers as R0R0 entries *)
Theorem complete_number_classification :
  forall m, m >= 1 ->
    (is_odd m /\ exists d n, d >= 1 /\ n >= 0 /\ m = valid_R1R0_entry_number d n) \/
    (is_even m /\ exists d n, d >= 1 /\ n >= 1 /\ m = valid_R0R0_entry_number d n).
Proof.
intros m Hm1.
destruct (Nat.even m) eqn:Heven_bool.
-
right.
split.
+
unfold is_even.
exact Heven_bool.
+
assert (H_even: is_even m).
{
unfold is_even.
exact Heven_bool.
}
apply even_eq_R0R0_entry_number; auto.
-
left.
split.
+
unfold is_odd.
exact Heven_bool.
+
assert (H_odd: is_odd m).
{
unfold is_odd.
exact Heven_bool.
}
apply odd_eq_R1R0_entry_number; auto.
Qed.

(* Power expansion: 3^(S k) = 3 * 3^k *)
Lemma pow3_expand : forall k, 3 ^ S k = 3 * 3 ^ k.
Proof.
  intros k. simpl. ring.
Qed.

(* Existence expression for 3^k being odd *)
Lemma pow3_is_odd : forall k, exists y, 3 ^ k = 2 * y + 1.
Proof.
  induction k as [| k IH].
  - exists 0. simpl. reflexivity.
  - destruct IH as [y Hy].
    exists (3 * y + 1).
    (* Rewrite 3^(S k) as 3 * 3^k, then substitute IH and finish. *)
    rewrite pow3_expand.
    rewrite Hy. simpl. ring.
Qed.

(* Existence expression for 3^k-1 being even *)
Lemma pow3_minus1_even : forall k, exists y, 3 ^ k - 1 = 2 * y.
Proof.
  intro k.
  destruct (pow3_is_odd k) as [y Hy].
  exists y. rewrite Hy. simpl. lia.
Qed.


(* 3^k >= 1 *)
Lemma pow3_ge1 : forall k, 1 <= 3 ^ k.
Proof.
  induction k; simpl; lia.
Qed.

(* Simple positivity lemma for 3^D (standard recursive definition of Nat.pow) *)
Lemma pow3_pos : forall D, 0 < 3 ^ D.
Proof.
induction D; simpl; lia.
Qed.






