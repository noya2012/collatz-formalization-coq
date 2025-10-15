Load "collatz_part_1.v". 


(* Helper lemma: when Nat.even n = false, n is odd *)
Lemma even_false_implies_odd : forall n,
  Nat.even n = false -> is_odd n.
Proof.
intros n Heven.
unfold is_odd.
exact Heven.
Qed.

(* Helper lemma: when Nat.even n = true, n is even *)
Lemma even_true_implies_even : forall n,
  Nat.even n = true -> is_even n.
Proof.
intros n Heven.
unfold is_even.
exact Heven.
Qed.


(* Any number greater than or equal to 1 is either odd or even *)
Lemma even_or_odd : forall n,
  n >= 1 -> is_even n \/ is_odd n.
Proof.
intros n H.
unfold is_even, is_odd.
destruct (Nat.even n) eqn:E.
- left. reflexivity.
- right. reflexivity.
Qed.

(* Immediate lemma: 2*x is always even *)
Lemma even_2x : forall x, Nat.even (2 * x) = true.
Proof.
  intros x. apply Nat.even_spec. exists x. reflexivity.
Qed.

(* Lemma: power of 2 is greater than 0 *)
Lemma gt_0_2_pow : forall n, 2^n > 0.
Proof.
induction n.
- simpl. lia.
- simpl. lia.
Qed.

(* Lemma: power of 2 is greater than or equal to 2 *)
Lemma pow2_ge_2 : forall n,
  n >= 1 -> 2^n >= 2.
Proof.
intros n H.
induction n.
- inversion H.
- simpl.
assert (H1: 2^n > 0) by apply gt_0_2_pow.
lia.
Qed.

(* Helper lemma: relationship between power of 2 and multiplication *)
Lemma pow2_mul_bound : forall d n,
  n >= 1 ->
  2 * (2^d) * n + 2^d <= 2^(d+2) * n.
Proof.
intros d n Hn.
replace (d+2) with (S (S d)) by lia.
simpl.
assert (H: 2^d > 0) by (apply gt_0_2_pow).
nia.
Qed.


(* pow2_monotone lemma *)
Lemma pow2_monotone : forall a b,
  a <= b -> 2^a <= 2^b.
Proof.
intros a b Hab.
induction b.
-
assert (a = 0) by lia.
subst. lia.
-
destruct (Nat.eq_dec a (S b)).
+
subst. lia.
+
assert (H: a <= b) by lia.
simpl.
assert (H1: 2^a <= 2^b) by (apply IHb; exact H).
assert (H2: 2^b > 0) by (apply gt_0_2_pow).
lia.
Qed.

(* pow2_gt_0 *)
Lemma pow2_gt_0 : forall n,
  2^n > 0.
Proof.
induction n.
- simpl. lia.
- simpl.
assert (H: 2^n + 2^n >= 2^n) by lia.
assert (H2: 2^n > 0) by assumption.
lia.
Qed.

Lemma pow2_strict_mono : forall a b,
  a < b -> 2^a < 2^b.
Proof.
intros a b Hlt.
induction Hlt.
-
simpl.
assert (H: 2^a > 0) by apply pow2_gt_0.
lia.
-
simpl.
assert (H: 2^m > 0) by apply pow2_gt_0.
lia.
Qed.

(* Properties of even numbers divided by 2 *)
Lemma even_div2_mul2 : forall k,
  k >= 1 ->
  (2 * k) / 2 = k.
Proof.
intros k Hk.
rewrite Nat.mul_comm.
apply Nat.div_mul.
lia.
Qed.




(* First prove the relationship between divmod and division *)
Lemma div2_divmod_eq : forall n,
  n / 2 = fst (divmod n 1 0 1).
Proof.
intros n.
unfold Nat.div.
reflexivity.
Qed.



(* Even number greater than or equal to 1 must be greater than or equal to 2 *)
Lemma even_ge_1_implies_ge_2 : forall n,
  n >= 1 ->
  is_even n ->
  n >= 2.
Proof.
intros n Hge1 Heven.
unfold is_even in Heven.
destruct n.
-
lia.
-
destruct n.
+
simpl in Heven.
discriminate.
+
lia.
Qed.


(* If n is even, then n can be expressed as a multiple of 2 *)
Lemma even_div_2 : forall n,
  valid_input n -> is_even n ->
  exists k, n = 2 * k.
Proof.
intros n Hvalid Heven.
unfold is_even in Heven.
apply Nat.even_spec in Heven.
destruct Heven as [k Hk].
exists k.
exact Hk.
Qed.

(* If n is even and divisible by 2^d, then n can be expressed as a multiple of 2^d *)
Lemma even_div_pow2 : forall n d,
  valid_input n -> d >= 1 -> is_even n ->
  (exists m, n = m * (2^d)) ->  (* New condition: n is divisible by 2^d *)
  exists k, n = k * (2^d).
Proof.
intros n d Hvalid Hd Heven Hdiv.
destruct Hdiv as [m Hm].
exists m.
exact Hm.
Qed.

(* Division by 2 preserves valid_input *)
Lemma div2_valid : forall n,
  valid_input n ->
  is_even n ->
  valid_input (n/2).
Proof.
intros n Hvalid Heven.
unfold valid_input in *.
assert (H: n >= 2).
{ apply even_ge_1_implies_ge_2; auto. }
apply Nat.div_le_lower_bound.
- lia.
- lia.
Qed.




(* Theorem: 2^d - 1 is odd *)
Lemma pow2_minus_1_odd : forall d,
  d >= 1 -> is_odd (2^d - 1).
Proof.
intros d Hd.
unfold is_odd.
induction d.
-
simpl. lia.
-
destruct d.
+
simpl. reflexivity.
+
assert (H_eq: 2^(S (S d)) = 2 * 2^(S d)).
{ simpl. ring. }
rewrite H_eq.
rewrite Nat.even_sub.
2:{
assert (H_gt_0: 2^(S d) > 0) by (apply pow2_gt_0).
lia.
}
simpl.
assert (H_simp: 2 ^ d + (2 ^ d + 0) + (2 ^ d + (2 ^ d + 0) + 0) = 4 * 2^d).
{ ring. }
rewrite H_simp.
assert (H_even: forall n, Nat.even (4 * n) = true).
{
intros n.
replace (4 * n) with (2 * (2 * n)) by ring.
apply Nat.even_mul.
}
rewrite H_even.
reflexivity.
Qed.

(* Theorem: There exists a d such that 2^d - 1 <= n *)
Lemma pow2_exists_le : forall n,
  valid_input n -> is_odd n ->
  exists d, d >= 1 /\ 2^d - 1 <= n.
Proof.
intros n Hvalid Hodd.
exists 1.
split.
- lia.
-
simpl.
assert (H_odd_ge_1: forall m, is_odd m -> m >= 1).
{
intros m Hm.
unfold is_odd in Hm.
destruct m.
- discriminate Hm.
- lia.
}
assert (H_n_ge_1: n >= 1).
{ apply H_odd_ge_1; auto. }
lia.
Qed.



(* 1. Basic property of 4 *)
Lemma four_eq_pow2_2 : 4 = 2^2.
Proof.
reflexivity.
Qed.

(* 2. Multiplication property of powers *)
Lemma pow_mul_r : forall a b c,
  (a^b)^c = a^(b*c).
Proof.
intros a b c.
induction c.
- simpl. rewrite Nat.mul_0_r. reflexivity.
- simpl.
rewrite IHc.
rewrite Nat.mul_succ_r.
rewrite <- Nat.pow_add_r.
f_equal.
lia.
Qed.

(* 3. Distributive property of powers *)
Lemma pow_distrib : forall a b c,
  a^(b + c) = a^b * a^c.
Proof.
intros.
apply Nat.pow_add_r.
Qed.

(* 4. Power expansion lemma for 4 *)
Lemma pow4_expand : forall k,
  4^k = 2^(2*k).
Proof.
intro k.
rewrite four_eq_pow2_2.
rewrite pow_mul_r.
reflexivity.
Qed.


(* Helper lemma: when d>=2, 2^d is even *)
Lemma pow2_even_when_ge_2 : forall d,
  d >= 2 -> is_even (2^d).
Proof.
intros d Hd.
unfold is_even.
destruct d as [|d'].
- lia.
- destruct d' as [|d''].
+ lia.
+
assert (H: exists k, 2^(S(S d'')) = 4 * k).
{ exists (2^d''). simpl. ring. }
destruct H as [k Hk].
rewrite Hk.
rewrite Nat.even_mul.
simpl. reflexivity.
Qed.


  (* Even number decomposition lemma *)
Lemma even_decomposition : forall n,
  is_even n -> exists k, n = 2 * k.
Proof.
intros n H.
unfold is_even in H.
rewrite Nat.even_spec in H.
destruct H as [k Hk].
exists k.
exact Hk.
Qed.

  (* Odd number decomposition lemma *)
Lemma odd_decomposition : forall n,
  is_odd n -> exists k, n = 2 * k + 1.
Proof.
intros n H.
unfold is_odd in H.
assert (H_odd: Nat.odd n = true).
{
unfold Nat.odd.
destruct (Nat.even n); simpl.
- discriminate H.
- reflexivity.
}
apply Nat.odd_spec in H_odd.
exact H_odd.
Qed.

(* Power of 2 odd decomposition lemma *)
Lemma power2_odd_decomposition : forall N,
  N >= 2 -> is_even N ->
  exists d q, d >= 1 /\ q >= 1 /\ N = 2^d * q /\ is_odd q.
Proof.
intros N HN_ge2 HN_even.
assert (H_aux: forall n, n >= 2 -> is_even n ->
exists d q, d >= 1 /\ q >= 1 /\ n = 2^d * q /\ is_odd q).
{
intros n.
pattern n.
apply (well_founded_induction lt_wf).
clear n.
intros n IH Hn_ge2 Hn_even.
apply even_decomposition in Hn_even as [k Hk].
assert (Hk_pos: k >= 1).
{
assert (Hk_pos_raw: k > 0).
{
destruct k as [| k'].
-
rewrite Hk in Hn_ge2.
simpl in Hn_ge2.
lia.
-
lia.
}
lia.
}
destruct (Nat.even k) eqn:Hk_even_bool.
-
assert (Hk_even: is_even k).
{
unfold is_even.
exact Hk_even_bool.
}
assert (Hk_ge2: k >= 2).
{
apply even_ge_1_implies_ge_2; auto.
}
assert (Hk_lt_n: k < n).
{
rewrite Hk.
lia.
}
apply IH in Hk_lt_n as [d' [q' [Hd' [Hq' [Heq' Hodd']]]]]; auto.
exists (d' + 1), q'.
repeat split.
+ lia.
+ exact Hq'.
+ rewrite Hk, Heq'.
rewrite Nat.pow_add_r.
simpl.
ring.
+ exact Hodd'.
-
assert (Hk_odd: is_odd k).
{
unfold is_odd.
exact Hk_even_bool.
}
exists 1, k.
repeat split.
+ lia.
+ exact Hk_pos.
+ rewrite Hk.
simpl.
ring.
+ exact Hk_odd.
}
apply H_aux; auto.
Qed.

(* 3n+1 outputs even number *)
Lemma even_3n_plus_1 : forall n,
  is_odd n ->
  is_even (3 * n + 1).
Proof.
intros n H_odd.
unfold is_odd, is_even in *.
rewrite Nat.even_add.
rewrite Nat.even_mul.
rewrite H_odd.
simpl.
reflexivity.
Qed.

(* 3n+1 preserves valid_input *)
Lemma valid_input_3n_plus_1 : forall n,
  valid_input n ->
  is_odd n ->
  valid_input (3 * n + 1).
Proof.
intros n Hn Hodd.
unfold valid_input in *.
lia.
Qed.