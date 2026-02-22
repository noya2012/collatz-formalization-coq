# odd_leads_R1R0_then_R0_pattern - Odd Numbers Pattern Transformation

## Basic Information

- **Theorem Type**: Theorem
- **Location**: collatz_part_16.v:5-59
- **Description**: Canonical pattern transformation theorem: odd numbers leading R1R0 sequence must be followed by R0

## Theorem Statement

```coq
Theorem odd_leads_R1R0_then_R0_pattern : forall m d n,
  m >= 1 -> d >= 1 -> n >= 0 -> m = valid_R1R0_entry_number d n ->
  exists Send,
    sequence_end m (repeat_R1R0 d) = Send /\
    is_even Send /\
    (2 * 3 ^ d * n <= Send /\ Send < 2 * 3 ^ d * (n + 1) /\ 3 ^ d - 1 <= Send) /\
    build_k_steps m (S d) = repeat_R1R0 d ++ [R0] /\
    (forall d' n', d' >= 1 -> n' >= 0 -> m = valid_R1R0_entry_number d' n' -> d' = d /\ n' = n).
```

## Theorem Purpose

This theorem establishes the **canonical pattern transformation** for odd numbers:
1. **R1R0 Output is Even**: After R1R0 sequence, result is even
2. **Next Operation**: Must be R0 (since result is even)
3. **Extended Pattern**: build_k_steps for S d steps equals R1R0^d + [R0]
4. **Uniqueness**: Parameters (d,n) are uniquely determined by m

## Theorem Properties

### Mathematical Properties
- **Parity Transition**: Odd → R1R0 → Even → R0 (next step)
- **Output Bounds**: Same strict bounds as R1R0 canonical form
- **Pattern Extension**: Builds on R1R0 by adding final R0
- **Parameter Uniqueness**: (d,n) uniquely represents m

### Structural Properties
- **R1R0 Phase**: D repetitions of R1R0
- **R0 Phase**: One additional R0 operation
- **Complete Pattern**: R1R0^d + R0 represents one "canonical step"
- **Deterministic Next**: The next operation is forced to be R0

## Technical Support

### Direct Dependencies

1. **build_k_steps_numeric_canonical**: Provides existence and uniqueness of canonical representation
2. **repeat_R1R0_output_even**: Proves R1R0 output is even (is_even Send = true)
3. **build_k_steps_Sn**: Relates build_k_steps m (S d) to build_k_steps m d

### Key Lemmas

1. **valid_R1R0_entry_number_properties**: Proves R1R0 entries are odd
2. **valid_R0R0_entry_number_properties**: Proves R0R0 entries are even (for contradiction)
3. **valid_R1R0_entry_number_odd**: Proves R1R0 entries produce odd numbers

## Sufficient and Necessary Support

### Sufficient Conditions
- If m is a valid R1R0 entry with parameters (d,n), then:
  - Output after d R1R0 operations is even
  - Next operation in build_k_steps is R0
  - Total pattern is R1R0^d ++ [R0]
  - Parameters (d,n) are unique

### Necessary Conditions
- The oddness of m forces the pattern to be R1R0, not R0R0
- The evenness of R1R0 output forces next operation to be R0

## Technical Features

### Proof Strategy

1. **Case Analysis**: Use build_k_steps_numeric_canonical to split into R1R0/R0R0 cases
2. **R1R0 Case** (main branch):
   - Use uniqueness to confirm we're in R1R0 branch
   - Define Send = output of R1R0 sequence
   - Prove Send is even using repeat_R1R0_output_even
   - Apply bounds from canonical representation
   - Show build_k_steps m (S d) = R1R0^d ++ [R0] using build_k_steps_Sn
   - Prove uniqueness of parameters
3. **R0R0 Case** (impossible):
   - Contradiction: R1R0 entry is odd, but R0R0 entry would be even

### Code Structure
```coq
Proof.
  intros m d n Hm Hd Hn Hrepr.
  pose proof (build_k_steps_numeric_canonical m Hm) as Hcanonical.
  destruct Hcanonical as [[d0 [...]] | [d0 [...]]].
  - // R1R0 case
    pose proof (Hunique0 d n ...) as [Hd_eq Hn_eq].
    subst d0 n0.
    set (Send := sequence_end m (repeat_R1R0 d)).
    // ... prove all properties
  - // R0R0 case - contradiction
    exfalso.
    // R1R0 entry is odd, R0R0 would be even - impossible
Qed.
```

### Key Technical Points

1. **Uniqueness Application**: Hunique0 shows no other (d',n') works
2. **Parity Proof**: Evenness of R1R0 output is critical
3. **Pattern Extension**: build_k_steps_Sn extends pattern by one step
4. **Contradiction**: R1R0 and R0R0 entries are disjoint (odd vs even)

## Applications and Significance

### Theoretical Significance
1. **Pattern Determinism**: Shows Collatz operations are deterministic at canonical level
2. **Alternating Structure**: Reveals R1R0 ↔ R0 alternation
3. **Canonical Steps**: Defines "canonical step" as R1R0^d + R0

### Practical Applications
1. **Sequence Construction**: Builds Collatz sequences from canonical patterns
2. **Pattern Recognition**: Identifies canonical steps in sequences
3. **Uniqueness**: Ensures unique decomposition of sequences

## Example Explanations

### Example 1: m=5, d=1, n=1
- Starting: 5 = valid_R1R0_entry_number 1 1
- R1R0 phase: 5 → 16 → 8
- Output: Send = 8 (even!)
- Bounds: 2*3^1*1 = 6 ≤ 8 < 12 = 2*3^1*(1+1), 3^1-1 = 2 ≤ 8
- Extended pattern: build_k_steps 5 2 = [R1; R0; R0]

### Example 2: m=3, d=2, n=0
- Starting: 3 = valid_R1R0_entry_number 2 0
- R1R0 phase: 3 → 10 → 5 → 16 → 8
- Output: Send = 8 (even!)
- Bounds: 2*3^2*0 = 0 ≤ 8 < 18 = 2*9*1, 9-1 = 8 ≤ 8
- Extended pattern: build_k_steps 3 3 = [R1; R0; R1; R0; R0]

### Example 3: m=11, d=2, n=1
- Starting: 11 = valid_R1R0_entry_number 2 1
- R1R0 phase: 11 → 34 → 17 → 52 → 26
- Output: Send = 26 (even!)
- Bounds: 2*9*1 = 18 ≤ 26 < 54 = 2*9*2, 9-1 = 8 ≤ 26

## Related Theorems

- **even_leads_R0_then_R1R0_pattern**: Complementary theorem for even numbers
- **build_k_steps_numeric_canonical**: Source of canonical representation
- **repeat_R1R0_output_even**: Proves R1R0 output is even
- **collatz_pattern_cycle_deterministic**: Global deterministic cycle pattern

## Historical Context

This theorem reveals fundamental **deterministic alternation**:
- Odd numbers → R1R0 pattern → Even output
- Even output → Must apply R0 → Back to odd
- This creates R1R0 ↔ R0 alternation

This is one of the key insights in understanding Collatz dynamics at the canonical pattern level.

## Connection to Collatz Conjecture

The alternating pattern R1R0 → R0 → R1R0 → R0 ... suggests:
1. **Deterministic Behavior**: At canonical level, Collatz is deterministic
2. **Cyclic Structure**: Patterns alternate between two canonical forms
3. **Growth Balance**: R1R0 (grows) and R0 (shrinks) balance each other

This theorem is crucial for understanding global behavior of Collatz sequences.
