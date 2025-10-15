Load "collatz_part_13.v".

(* Odd Branch Existence Lemma *)
Lemma odd_branch_existence : forall n', n' >= 0 -> Nat.even (S n') = false ->
  exists t odd, odd >= 1 /\ is_odd odd /\ S n' = odd * 2^t.
Proof.
intros n' Hn' Hev.
exists 0, (S n').
split; [lia|].
split.
- unfold is_odd; exact Hev.
- simpl; lia.
Qed.

(* Normalize R0R0 entry (d,n) to n' odd (absorbing 2 factors from n), preserving value *)
Lemma R0R0_canonical_factorization :
  forall d n, d >= 1 -> n >= 1 ->
    exists d' n', d' >= 1 /\ n' >= 1 /\ is_odd n' /\
                  valid_R0R0_entry_number d n = valid_R0R0_entry_number d' n'.
Proof.
intros d n Hd Hn.
destruct (Nat.even n) eqn:Heven.
-
assert (Hn_ge2 : n >= 2).
{ destruct n as [|n']; [lia|].
destruct n'; [simpl in Heven; discriminate| lia]. }
assert (Hn_even : is_even n) by (unfold is_even; exact Heven).
destruct (power2_odd_decomposition n Hn_ge2 Hn_even)
as [d0 [q [Hd0 [Hq [Heqn Hoddq]]]]].
exists (d + d0), q.
split; [lia|].
split; [exact Hq|].
split; [exact Hoddq|].
unfold valid_R0R0_entry_number.
rewrite Heqn.
replace (2 ^ d0 * q) with (q * 2 ^ d0) by (apply Nat.mul_comm).
replace ((q * 2 ^ d0) * 2 ^ d) with (q * (2 ^ d0 * 2 ^ d)) by (rewrite Nat.mul_assoc; reflexivity).
rewrite Nat.mul_comm with (n := 2 ^ d0) (m := 2 ^ d).
rewrite <- Nat.pow_add_r.
reflexivity.
-
exists d, n.
split; [exact Hd|].
split; [exact Hn|].
split; [unfold is_odd; exact Heven|].
reflexivity.
Qed.

(* Complete Number Canonical Classification: Every positive integer uniquely belongs to R1R0 or R0R0 branch *)
Theorem complete_number_canonical_classification :
  forall m, m >= 1 ->
    (exists d n,
        d >= 1 /\ n >= 0 /\
        m = valid_R1R0_entry_number d n /\
        (* Uniqueness: Any other R1R0 representation is identical to (d,n) *)
        (forall d' n', d' >= 1 -> n' >= 0 ->
           m = valid_R1R0_entry_number d' n' -> d' = d /\ n' = n)) \/
    (exists d n,
        d >= 1 /\ n >= 1 /\ is_odd n /\
        m = valid_R0R0_entry_number d n /\
        (forall d' n', d' >= 1 -> n' >= 1 -> is_odd n' ->
           m = valid_R0R0_entry_number d' n' -> d' = d /\ n' = n)).
Proof.
intros m Hm.
destruct (complete_number_classification m Hm)
as [ [Hodd [d [n [Hd [Hn Hrepr]]]]] |
[Heven [d [n [Hd [Hn Hrepr]]]]] ].
-
left.
exists d, n.
split; [exact Hd|].
split; [exact Hn|].
split; [exact Hrepr|].
intros d2 n2 Hd2 Hn2 Hrepr'.
pose proof Hrepr as H1.
assert (is_odd m) as Hoddm by assumption.
destruct (R1R0_decomposition_unique m d d2 n n2
Hoddm Hd Hd2 Hn Hn2 Hrepr Hrepr') as [Hd_eq Hn_eq].
split; [symmetry; exact Hd_eq| symmetry; exact Hn_eq].
-
right.
destruct (R0R0_canonical_factorization d n Hd Hn)
as [d' [n' [Hd' [Hn' [Hodd' Heq]]]]].
assert (Hm' : m = valid_R0R0_entry_number d' n').
{ rewrite Hrepr. exact Heq. }
exists d', n'.
split; [exact Hd'|].
split; [exact Hn'|].
split; [exact Hodd'|].
split; [exact Hm'|].
intros d1 n1 Hd1 Hn1 Hodd1 Hrepr1.
destruct (R0R0_decomposition_unique m d' d1 n' n1 Hm' Hrepr1 Hodd' Hodd1)
as [Hd_eq Hn_eq].
split; [symmetry; exact Hd_eq| symmetry; exact Hn_eq].
Qed.



(* R1R0 Strict Upper Bound: Prove S is strictly less than 2*3^d*(n+1) *)
Lemma tighten_R1R0_strict_upper : forall d n S,
  d >= 1 ->
  2 * 3 ^ d * n <= S ->
  S <= 3 ^ d * (2 * n + 1) ->
  S < 2 * 3 ^ d * (n + 1).
Proof.
intros d n S Hd Hlow Hup.
replace (3 ^ d * (2 * n + 1)) with (2 * 3 ^ d * n + 3 ^ d) in Hup by lia.
assert (Hlt: 3 ^ d < 2 * 3 ^ d).
{
rewrite <- Nat.mul_1_l at 1.
apply Nat.mul_lt_mono_pos_r.
-
apply pow3_pos; lia.
- lia.
}
apply Nat.le_lt_trans with (2 * 3 ^ d * n + 3 ^ d).
- exact Hup.
-
lia.
Qed.
(* R1R0 entry number itself is odd (d>=1 case) *)
Lemma valid_R1R0_entry_number_is_odd : forall d n,
  d >= 1 -> n >= 0 -> is_odd (valid_R1R0_entry_number d n).
Proof.
intros d n Hd Hn.
unfold is_odd.
pose proof (valid_R1R0_entry_number_plus1 d n) as Hplus.
set (m := valid_R1R0_entry_number d n) in *.
assert (Heven_pow: Nat.even (2 ^ d) = true) by (apply power_2_even_property; lia).
assert (Hodd_factor: Nat.even (2 * n + 1) = false).
{ rewrite Nat.even_add, Nat.even_mul. simpl. reflexivity. }
assert (Heven_m1: Nat.even (m + 1) = true).
{ rewrite Hplus. rewrite Nat.even_mul, Heven_pow, Hodd_factor. simpl. reflexivity. }
replace (m + 1) with (S m) in Heven_m1 by lia.
rewrite Nat.even_succ in Heven_m1.
apply Bool.negb_true_iff in Heven_m1; exact Heven_m1.
Qed.



(* Intermediate Lemma: Core auxiliary lemma for simplifying branch logic *)
Lemma R0R0_branch_simplification : forall d n dc nc,
  d >= 1 -> n >= 1 -> dc >= 1 -> nc >= 1 -> is_odd nc ->
  valid_R0R0_entry_number d n = valid_R0R0_entry_number dc nc ->
  (exists d0, dc = d + d0 /\ n = nc * 2 ^ d0) \/ (dc = d /\ n = nc).
Proof.
intros d n dc nc Hd Hn Hdc Hnc Hoddnc Heq.
unfold valid_R0R0_entry_number in Heq.
rewrite Nat.mul_comm in Heq.
rewrite Nat.mul_comm in Heq.
destruct (Nat.even n) eqn:Heven.
-
left.
assert (Hn_even : is_even n) by (apply even_true_implies_even; exact Heven).
assert (Hn_ge2 : n >= 2).
{ apply even_ge_1_implies_ge_2; [lia | exact Hn_even]. }
apply power2_odd_decomposition in Hn_even as [d0 [q [Hd0 [Hq [Heqnq Hoddq]]]]]; auto.
rewrite Heqnq in Heq.
assert (Hnorm : 2 ^ (d0 + d) * q = 2 ^ dc * nc).
{ rewrite Nat.pow_add_r by lia.
rewrite <- Nat.mul_assoc.
rewrite (Nat.mul_comm (2 ^ d) q).
rewrite Nat.mul_assoc.
rewrite Heq.
rewrite Nat.mul_comm.
reflexivity. }
assert (Hd_sum : d0 + d >= 1) by lia.
pose proof (pow2_times_odd_unique (d0 + d) dc q nc Hd_sum Hdc Hoddq Hoddnc Hnorm)
as [Hddc Hqnc].
exists d0; split.
+ rewrite Nat.add_comm; symmetry; exact Hddc.
+ rewrite Heqnq; rewrite Hqnc; rewrite (Nat.mul_comm (2 ^ d0) nc); reflexivity.
-
right.
assert (Hn_odd : is_odd n) by (apply even_false_implies_odd; exact Heven).
rewrite Nat.mul_comm in Heq.
rewrite (Nat.mul_comm nc (2 ^ dc)) in Heq.
pose proof (pow2_times_odd_unique d dc n nc Hd Hdc Hn_odd Hoddnc Heq)
as [Hddc Hnnc].
split; [symmetry; exact Hddc | exact Hnnc].
Qed.

(* R0R0 Uniqueness Helper: Through canonical decomposition, any entry uniquely corresponds to odd parameters *)
Lemma R0R0_unique_via_canonical :
  forall m d n d' n',
    d >= 1 -> n >= 1 -> is_odd n' ->
    m = valid_R0R0_entry_number d n ->
    m = valid_R0R0_entry_number d' n' ->
    exists d1 n1,
      d1 >= 1 /\ n1 >= 1 /\ is_odd n1 /\
      m = valid_R0R0_entry_number d1 n1 /\
      d' = d1 /\ n' = n1 /\
      (exists d0, d1 = d + d0 /\ n = n1 * 2 ^ d0).
Proof.
intros m d n d' n' Hd Hn Hodd' Hmdef Hmdef'.
destruct (R0R0_canonical_factorization d n Hd Hn)
as [dc [nc [Hdc [Hnc [Hoddnc Heqcanon]]]]].
assert (Hmcanon : m = valid_R0R0_entry_number dc nc) by (rewrite Hmdef; exact Heqcanon).
destruct (R0R0_decomposition_unique m dc d' nc n' Hmcanon Hmdef' Hoddnc Hodd')
as [Hd_eq Hn_eq].
exists dc, nc.
repeat split; try assumption; try (symmetry; assumption).
unfold valid_R0R0_entry_number in Heqcanon.
destruct (R0R0_branch_simplification d n dc nc Hd Hn Hdc Hnc Hoddnc Heqcanon)
as [[d0 [Hd0_eq Hn_rel]] | [Hdc_eq Hnc_eq]].
-
exists d0; split.
+ exact Hd0_eq.
+ exact Hn_rel.
-
exists 0; split.
+ rewrite Hdc_eq; lia.
+ rewrite Hnc_eq; simpl; lia.
Qed.

(* Every positive integer m uniquely corresponds to canonical representation of R1R0 or R0R0 branch with determined bounds *)
Theorem build_k_steps_numeric_canonical :
  forall m, m >= 1 ->
   (exists d n,
      d >= 1 /\ n >= 0 /\
      m = valid_R1R0_entry_number d n /\
      build_k_steps m d = repeat_R1R0 d /\
      let S := sequence_end m (repeat_R1R0 d) in
        (2*3 ^ d*n <= S /\ S < 2*3 ^ d*(n+1) /\ 3 ^ d - 1 <= S) /\
        (forall d' n', d' >= 1 -> n' >= 0 ->
          m = valid_R1R0_entry_number d' n' -> d'=d /\ n'=n)) \/
   (exists d n,
      d >= 1 /\ n >= 1 /\ is_odd n /\
      m = valid_R0R0_entry_number d n /\
      build_k_steps m d = repeat_R0 d /\
      sequence_end m (repeat_R0 d) = n /\
      (forall d' n', d' >= 1 -> n' >= 1 -> is_odd n' ->
        m = valid_R0R0_entry_number d' n' -> d'=d /\ n'=n)).
Proof.
intros m Hm.
destruct (build_k_steps_numeric_bounds_exists m Hm) as
[  [d [n [Hd [Hn [Hmdef [Hbuild [Hlow_lin [Hlow_const Hup]]]]]]]]
|  [d [n [Hd [Hn [Hmdef [Hbuild [Hn_ge1 [Hn_le_m Heq]]]]]]]] ].
- left.
set (Send := sequence_end (valid_R1R0_entry_number d n) (repeat_R1R0 d)).
assert (Hstrict: Send < 2 * 3 ^ d * (n + 1)).
{ apply tighten_R1R0_strict_upper; try lia.
all: unfold Send; assumption. }
exists d, n.

split; [exact Hd|].
split; [exact Hn|].
split; [exact Hmdef|].
split; [exact Hbuild|].
split.
*
unfold Send.
rewrite Hmdef.
repeat split; [exact Hlow_lin| exact Hstrict | exact Hlow_const].
*
intros d' n' Hd' Hn' Hrepr'.
assert (is_odd m) as Hoddm by (rewrite Hmdef; apply valid_R1R0_entry_number_is_odd; lia).
destruct (R1R0_decomposition_unique m d d' n n' Hoddm Hd Hd' Hn Hn' Hmdef Hrepr') as [Hd_eq Hn_eq].
split; [symmetry; exact Hd_eq | symmetry; exact Hn_eq].
- right.
destruct (R0R0_canonical_factorization d n Hd Hn) as [dc [nc [Hdc [Hnc [Hoddnc Heq_canon]]]]].
assert (Hmcanon : m = valid_R0R0_entry_number dc nc) by (rewrite Hmdef; exact Heq_canon).
exists dc, nc.
split; [ exact Hdc |].
split; [ exact Hnc |].
split; [ exact Hoddnc |].
split; [ exact Hmcanon |].
split.
{ destruct (R0R0_branch_simplification d n dc nc Hd Hn Hdc Hnc Hoddnc Heq_canon)
as [[d0 [Hd0_eq Hn_rel]] | [Hdc_eq Hnc_eq]].
- rewrite Hmcanon. apply build_k_steps_on_valid_R0R0; assumption.
- rewrite Hdc_eq. exact Hbuild. }
split.
{ rewrite Hmcanon.
destruct (R0R0_branch_simplification d n dc nc Hd Hn Hdc Hnc Hoddnc Heq_canon)
as [[d0 [Hd0_eq Hn_rel]] | [Hdc_eq Hnc_eq]].
- apply (repeat_R0_output_reaches_one dc nc); assumption.
- rewrite Hdc_eq. rewrite <- Hnc_eq. apply (repeat_R0_output_reaches_one d n); assumption. }
intros d' n' Hd' Hn' Hodd' Hrepr'.
destruct (@R0R0_decomposition_unique m dc d' nc n' Hmcanon Hrepr' Hoddnc Hodd') as [HdEq HnEq].
split; [ symmetry; exact HdEq | symmetry; exact HnEq ].
Qed.
