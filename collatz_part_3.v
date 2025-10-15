Load "collatz_part_2.v".

(* R0R1 entry number can be expressed as a multiple of 2 *)
Theorem valid_R0R1_entry_number_produces_d_R0R1 : forall d n,
  d >= 1 ->
  n >= 1 ->
  exists k, valid_R0R1_entry_number d n = 2 * k.
Proof.
intros d n Hd Hn.
unfold valid_R0R1_entry_number.
exists ((2^d * n) + (2^(d-1) - 1)).
destruct d.
-
inversion Hd.
-
simpl.
replace (d - 0) with d by lia.
repeat rewrite Nat.add_0_r.
assert (H1: 2^d + 2^d = 2 * 2^d) by lia.
repeat rewrite H1.
assert (H2: 2 * 2^d + 2 * 2^d = 4 * 2^d) by lia.
rewrite H2.
nia.
Qed.

(* R0R1 entry number is greater than or equal to 1 *)
Theorem valid_R0R1_entry_number_induction : forall d n,
  d >= 1 ->
  n >= 1 ->
  valid_R0R1_entry_number d n >= 1.
Proof.
intros d n Hd Hn.
induction d as [| d' IH].
-
inversion Hd.
-
unfold valid_R0R1_entry_number.
simpl.
repeat rewrite Nat.add_0_r.
assert (H1: 2^d' > 0) by apply gt_0_2_pow.
assert (H2: n >= 1) by exact Hn.
assert (H3: 2^d' + 2^d' = 2 * 2^d') by lia.
repeat rewrite H3.
assert (H4: 2 * 2^d' + 2 * 2^d' = 4 * 2^d') by lia.
rewrite H4.
nia.
Qed.

(* R1R0 entry number is greater than or equal to 1 *)
Theorem valid_R1R0_entry_number_induction : forall d n,
  d >= 1 ->
  n >= 1 ->
  valid_R1R0_entry_number d n >= 1.
Proof.
intros d n Hd Hn.
unfold valid_R1R0_entry_number.
induction d as [| d' IH].
-
inversion Hd.
-
simpl.
repeat rewrite Nat.add_0_r.
assert (H1: 2^d' > 0) by apply gt_0_2_pow.
assert (H2: n >= 1) by exact Hn.
assert (H3: 2^d' + 2^d' = 2 * 2^d') by lia.
repeat rewrite H3.
assert (H4: 2 * 2^d' + 2 * 2^d' = 4 * 2^d') by lia.
rewrite H4.
nia.
Qed.

(* R1R0 entry number can be expressed as 2k+1 *)
Theorem valid_R1R0_entry_number_produces_d_R1R0 : forall d n,
  d >= 1 ->
  n >= 1 ->
  exists k, valid_R1R0_entry_number d n = 2 * k + 1.
Proof.
intros d n Hd Hn.
unfold valid_R1R0_entry_number, valid_R0R1_entry_number.
assert (H: exists k, (2 * (2^d) * n) + (2^d - 2) = 2 * k).
{ apply valid_R0R1_entry_number_produces_d_R0R1; assumption. }
destruct H as [k H].
exists k.
assert (H0: 2^d >= 2).
{ apply pow2_ge_2. exact Hd. }
assert (H1: (2 * (2^d) * n) + (2^d - 1) =
((2 * (2^d) * n) + (2^d - 2)) + 1).
{
rewrite <- Nat.add_assoc.
f_equal.
lia.
}
rewrite H1.
rewrite H.
reflexivity.
Qed.



(* R0R0 entry number is greater than or equal to 1 *)
Theorem valid_R0R0_entry_induction : forall d n,
  d >= 1 ->
  n >= 1 ->
  valid_R0R0_entry_number d n >= 1.
Proof.
intros d n Hd Hn.
unfold valid_R0R0_entry_number.
assert (H1: 2^d > 0) by (apply gt_0_2_pow).
assert (H2: n * 2^d >= 1 * 2^d).
{ apply Nat.mul_le_mono_nonneg_r; try lia. }
lia.
Qed.

(* R0R0 entry number can be expressed as a multiple of 2^d *)
Theorem valid_R0R0_entry_number_produces_d_R0 : forall d n,
  d >= 1 ->
  n >= 1 ->
  exists k, valid_R0R0_entry_number d n = 2^d * k.
Proof.
intros d n Hd Hn.
unfold valid_R0R0_entry_number.
exists n.
rewrite Nat.mul_comm.
reflexivity.
Qed.

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

(* Multiple R0R0 representation ways for any even number *)
Lemma even_multiple_R0R0_representations :
  forall m, m >= 1 -> is_even m ->
    forall d, d >= 1 ->
      (m mod (2^d) = 0) ->
      exists n, n >= 1 /\ m = valid_R0R0_entry_number d n.
Proof.
intros m Hm1 Heven d Hd Hmod.
assert (H_exists: exists n, m = n * 2^d).
{
apply Nat.mod_divide in Hmod.
- exact Hmod.
-
assert (H_pos: 2^d > 0) by apply gt_0_2_pow.
lia.
}
destruct H_exists as [n Hn].
assert (Hn_ge1: n >= 1).
{
destruct n as [| n'].
-
rewrite Hn in Hm1.
simpl in Hm1.
lia.
-
lia.
}
exists n.
split.
- exact Hn_ge1.
- unfold valid_R0R0_entry_number.
exact Hn.
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

(* 2*y divided by 2 equals y *)
Lemma twice_div : forall y, (2 * y) / 2 = y.
Proof.
  intros y.
  rewrite (Nat.mul_comm 2 y).
  apply Nat.div_mul; lia.
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

(* Strict subtraction positivity lemma *)
Lemma sub_pos_strict : forall a b, a < b -> 0 < b - a.
Proof.
intros a b H; lia.
Qed.

(* Natural number multiplication positivity lemma: product of two positive numbers is positive *)
Lemma mul_pos_pos_nat : forall a b, 0 < a -> 0 < b -> 0 < a * b.
Proof.
intros a b Ha Hb.
destruct a; [lia|]. simpl. lia.
Qed.

(* Decompose any natural number >=2 into 2^d * q, where q is odd. *)
Lemma nat_decompose_pow2_odd : forall m,
  m >= 2 -> exists d q, m = 2^d * q /\ is_odd q.
Proof.
  intros m Hm.
  destruct (Nat.even m) eqn:Heven.
  - (* even case: use existing decomposition lemma *)
    assert (H_even : is_even m) by (unfold is_even; exact Heven).
    destruct (power2_odd_decomposition m Hm H_even) as [d [q [Hd [Hq [Heq Hodd]]]]].
    exists d, q. split; [assumption | assumption].
  - (* odd case: take d = 0, q = m *)
    exists 0. exists m. split. 
    + simpl. lia.
    + unfold is_odd. exact Heven.
Qed.
