Load "collatz_part_14.v".

(* Using canonical decomposition to derive logarithmic upper bounds for d (R1R0 branch) *)
Lemma canonical_R1R0_d_log2_bound :
  forall m d n,
    m >= 1 ->
    m = valid_R1R0_entry_number d n ->
    d >= 1 -> n >= 0 ->
    2 ^ d <= m + 1 /\ d <= log2 (m + 1).
Proof.
intros m d n Hm Hrepr Hd Hn.
unfold valid_R1R0_entry_number in Hrepr.
assert (Hpow: 2 ^ d <= m + 1).
{ rewrite Hrepr. lia. }
split.
- exact Hpow.
-
assert (Hpos: m + 1 >= 1) by lia.
pose proof (Nat.log2_spec (m + 1) Hpos) as [_ Hhigh].
destruct (Nat.le_gt_cases d (log2 (m + 1))) as [Hle | Hgt].
+ exact Hle.
+
assert (Hge: S (log2 (m + 1)) <= d) by lia.
assert (Hpow2: 2 ^ (S (log2 (m + 1))) <= 2 ^ d) by (apply Nat.pow_le_mono_r; lia).
lia.
Qed.

(* R0R0 branch *)
Lemma canonical_R0R0_d_log2_bound :
  forall m d n,
    m >= 1 ->
    m = valid_R0R0_entry_number d n ->
    d >= 1 -> n >= 1 ->
    2 ^ d <= m /\ d <= log2 m.
Proof.
intros m d n Hm Hrepr Hd Hn.
unfold valid_R0R0_entry_number in Hrepr.
assert (Hpow: 2 ^ d <= m).
{ rewrite Hrepr.
assert (Hpow_pos: 2^d > 0) by (apply gt_0_2_pow; exact Hd).
rewrite <- Nat.mul_1_l at 1.
apply Nat.mul_le_mono_r; lia. }
split.
- exact Hpow.
-
assert (Hpos: m >= 1) by lia.
pose proof (Nat.log2_spec m Hpos) as [_ Hhigh].
destruct (Nat.le_gt_cases d (log2 m)) as [Hle | Hgt].
+ exact Hle.
+ assert (Hge: S (log2 m) <= d) by lia.
assert (Hpow2: 2 ^ (S (log2 m)) <= 2 ^ d) by (apply Nat.pow_le_mono_r; lia).
lia.
Qed.

(* Unified wrapper: For any canonical branch, d <= log2 (m+2) *)
Lemma canonical_d_log2_global :
  forall m d n,
    m >= 1 ->
    ( (m = valid_R1R0_entry_number d n /\ d >= 1 /\ n >= 0)
    \/ (m = valid_R0R0_entry_number d n /\ d >= 1 /\ n >= 1) ) ->
    d <= log2 (m + 2).
Proof.
intros m d n Hm [Hcase | Hcase].
- destruct Hcase as [Hrepr [Hd Hn]].
pose proof (canonical_R1R0_d_log2_bound m d n Hm Hrepr Hd Hn) as [Hpow Hlog].
apply Nat.le_trans with (log2 (m+1)); [exact Hlog|].
apply log2_monotone. lia.
- destruct Hcase as [Hrepr [Hd Hn]].
pose proof (canonical_R0R0_d_log2_bound m d n Hm Hrepr Hd Hn) as [Hpow Hlog].
apply Nat.le_trans with (log2 m); [exact Hlog|].
apply log2_monotone. lia.
Qed.


