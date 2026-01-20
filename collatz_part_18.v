Load "collatz_part_17.v".

(* Valid chains condition non-empty list with valid chain sequence conditions *)
Definition valid_chains_condition
  (chains : list (bool * nat * nat * nat * nat)) : Prop :=
  chains <> nil /\
  (forall bdnds, In bdnds chains ->
    let '(b, d, n, m, Send) := bdnds in
    valid_chain_sequence_condition b d n m Send).

(* Chains R0 advantage R0 operations exceed R1 operations with specific difference *)
Definition chains_R0_advantage
  (chains : list (bool * nat * nat * nat * nat)) : Prop :=
  let total_seq := concat (map (fun '(b, d, _, _, _) => canonical_chain b d) chains) in
  let simple_chains := extract_simple_chains chains in
  fst (count_operations total_seq) > snd (count_operations total_seq) /\
  fst (count_operations total_seq) - snd (count_operations total_seq) =
    sum_contributions simple_chains.

(* Universal R0 advantage bounds precise counts for canonical chains *)
Corollary universal_R0_advantage_bounds :
  forall b d, d >= 1 ->
  let '(r0s, r1s) := count_operations (canonical_chain b d) in
  match b with
  | true => r0s = d + 1 /\ r1s = d /\ r0s = r1s + 1 /\ r0s <= 2 * r1s
  | false => r0s = d + 1 /\ r1s = 1 /\ r0s = (d + 1) * r1s /\ r0s >= 2 * r1s
  end.
Proof.
intros b d Hd.
destruct b.
- pose proof (count_operations_canonical_chain true d Hd) as Hcount.
rewrite Hcount. repeat split; lia.
- pose proof (count_operations_canonical_chain false d Hd) as Hcount.
rewrite Hcount. repeat split; lia.
Qed.

(* Valid sequence concatenation combining two valid sequences *)
Lemma valid_sequence_app :
  forall (n : nat) (ops1 ops2 : list CollatzOp),
    valid_sequence ops1 n ->
    valid_sequence ops2 (sequence_end n ops1) ->
    valid_sequence (ops1 ++ ops2) n.
Proof.
intros n ops1 ops2 H1 H2.
unfold valid_sequence in *.
intros i Hi.
rewrite app_length in Hi.
destruct (lt_dec i (length ops1)) as [Hi1 | Hi1].
-
rewrite app_nth1 by lia.
apply H1; lia.
-
assert (Hge : length ops1 <= i) by lia.
rewrite app_nth2 by exact Hge.
set (j := i - length ops1).
assert (Hj : j < length ops2) by (unfold j; lia).
assert (Hnv : nth_sequence_value n i = nth_sequence_value (sequence_end n ops1) j).
{
assert (Hi_eq : i = length ops1 + j) by (unfold j; lia).
rewrite Hi_eq.
rewrite nth_sequence_value_app.
unfold sequence_end.
reflexivity.
}
rewrite Hnv.
apply H2.
exact Hj.
Qed.

(* Logarithm of product with power of 2 log2q * 2^d = log2q + d *)
Lemma log2_mul_pow2 :
  forall (q d : nat),
    q > 0 ->
    log2 (q * 2 ^ d) = log2 q + d.
Proof.
intros q d Hq.
induction d as [|d IH].
- simpl. rewrite Nat.mul_1_r. lia.
- rewrite Nat.pow_succ_r'.
replace (q * (2 * 2 ^ d)) with (2 * (q * 2 ^ d)) by ring.
rewrite log2_mult_power2.
+ rewrite IH. lia.
+ apply Nat.mul_pos_pos.
* lia.
* apply gt_0_2_pow.
Qed.

(* Log2 bound for R1R0 entry depth d <= log2m + 1 *)
Lemma R1R0_entry_d_log2_bound :
  forall m d n,
    m >= 1 ->
    m = valid_R1R0_entry_number d n ->
    d >= 1 ->
    n >= 0 ->
    d <= log2 (m + 1).
Proof.
intros m d n Hm Hrepr Hd Hn.
unfold valid_R1R0_entry_number in Hrepr.
assert (Hpow : 2 ^ d <= m + 1).
{ rewrite Hrepr. lia. }
assert (Hpos : m + 1 >= 1) by lia.
pose proof (Nat.log2_spec (m + 1) Hpos) as [_ Hhigh].
destruct (Nat.le_gt_cases d (log2 (m + 1))) as [Hle | Hgt].
- exact Hle.
- assert (Hge : S (log2 (m + 1)) <= d) by lia.
assert (Hpow2 : 2 ^ (S (log2 (m + 1))) <= 2 ^ d)
by (apply Nat.pow_le_mono_r; lia).
lia.
Qed.

(* Extract simple chains concatenation distributes over list append *)
Lemma extract_simple_chains_app :
  forall chains1 chains2,
    extract_simple_chains (chains1 ++ chains2) =
    extract_simple_chains chains1 ++ extract_simple_chains chains2.
Proof.
induction chains1 as [|a chains1 IH]; simpl; intros; auto.
destruct a as [b d]; simpl.
rewrite IH; auto.
Qed.

(* Sum contributions concatenation additive over list append *)
Lemma sum_contributions_app :
  forall chains1 chains2,
    sum_contributions (chains1 ++ chains2) =
    sum_contributions chains1 + sum_contributions chains2.
Proof.
induction chains1 as [|a chains1 IH]; simpl; intros; auto.
destruct a as [b d]; simpl.
rewrite IH; lia.
Qed.

(* Chains R0 advantage concatenation preserved under list append *)
Lemma chains_R0_advantage_app :
  forall chains1 chains2,
    chains_R0_advantage chains1 ->
    chains_R0_advantage chains2 ->
    chains_R0_advantage (chains1 ++ chains2).
Proof.
intros chains1 chains2 H1 H2.
unfold chains_R0_advantage in *.
destruct H1 as [Hgt1 Heq1].
destruct H2 as [Hgt2 Heq2].
split.
-
rewrite map_app, concat_app.
rewrite count_operations_app.
simpl.
destruct (count_operations (concat (map (fun '(b, d, _, _, _) => canonical_chain b d) chains1))) as [r0s1 r1s1].
destruct (count_operations (concat (map (fun '(b, d, _, _, _) => canonical_chain b d) chains2))) as [r0s2 r1s2].
simpl in Hgt1, Hgt2.
simpl.
lia.
-
rewrite map_app, concat_app.
rewrite count_operations_app.
rewrite extract_simple_chains_app, sum_contributions_app.
simpl.
destruct (count_operations (concat (map (fun '(b, d, _, _, _) => canonical_chain b d) chains1))) as [r0s1 r1s1].
destruct (count_operations (concat (map (fun '(b, d, _, _, _) => canonical_chain b d) chains2))) as [r0s2 r1s2].
simpl in Hgt1, Hgt2, Heq1, Heq2.
simpl.
lia.
Qed.