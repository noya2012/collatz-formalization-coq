# even_leads_R0_then_R1R0_pattern - Even Numbers Pattern Transformation

## Basic Information

- **Theorem Type**: Theorem
- **Location**: collatz_part_16.v:63-127
- **Description**: Canonical pattern transformation theorem: even numbers leading R0 sequence must be followed by R1R0

## Theorem Statement

```coq
Theorem even_leads_R0_then_R1R0_pattern : forall m d n,
  m >= 1 -> d >= 1 -> n >= 1 -> is_odd n -> m = valid_R0R0_entry_number d n ->
  exists Send,
    sequence_end m (repeat_R0 d) = Send /\
    is_odd Send /\
    Send = n /\
    build_k_steps m (S d) = repeat_R0 d ++ [R1; R0] /\
    (forall d' n', d' >= 1 -> n' >= 1 -> is_odd n' -> m = valid_R0R0_entry_number d' n' -> d' = d /\ n' = n).
```

## Theorem Purpose

This theorem establishes the **complementary pattern transformation** for even numbers:
1. **R0 Output is Odd**: After R0 sequence, result is odd
2. **Next Operations**: Must be R1 then R0 (since result is odd)
3. **Extended Pattern**: build_k_steps for S d steps equals R0^d + [R1; R0]
4. **Uniqueness**: Parameters (d,n) are uniquely determined by m (with odd n requirement)

## Theorem Properties

### Mathematical Properties
- **Parity Transition**: Even → R0^d → Odd → R1R0 (next steps)
- **Exact Output**: After d R0 operations, output = n (exact, not just bounds)
- **Pattern Extension**: Builds on R0^d by adding final R1R0
- **Parameter Uniqueness**: (d,n) uniquely represents m when n is odd

### Structural Properties
- **R0 Phase**: D divisions by 2
- **R1R0 Phase**: One R1R0 pair (R1, R0)
- **Complete Pattern**: R0^d + [R1; R0] represents one "canonical step"
- **Deterministic Next**: The next operations are forced to be R1 then R0

### Comparison with Odd Counterpart

| Property | odd_leads_R1R0_then_R0_pattern | even_leads_R0_then_R1R0_pattern |
|----------|-----------------------------------|--------------------------------------|
| Input Type | Odd (R1R0 entry) | Even (R0R0 entry) |
| Output Parity | Even | Odd |
| Next Operation | R0 (single) | R1 then R0 (pair) |
| Pattern Extension | R1R0^d + [R0] | R0^d + [R1; R0] |
| Uniqueness Condition | n ≥ 0 | n ≥ 1 + is_odd n |

## Technical Support

### Direct Dependencies

1. **build_k_steps_numeric_canonical**: Provides existence and uniqueness of canonical representation
2. **build_k_steps_Sn**: Relates build_k_steps m (S d) to build_k_steps m d
3. **R0R0_decomposition_unique**: Proves uniqueness of (d,n) representation with odd n

### Key Lemmas

1. **valid_R0R0_entry_number_properties**: Proves R0R0 entries are even (for contradiction in odd branch)
2. **valid_R1R0_entry_number_properties**: Proves R1R0 entries are odd (for contradiction in even branch)
3. **R0R0_output_exact_n**: Output after d R0 operations equals n

## Sufficient and Necessary Support

### Sufficient Conditions
- If m is a valid R0R0 entry with odd n and parameters (d,n), then:
  - Output after d R0 operations equals n (which is odd)
  - Next operations in build_k_steps are R1 then R0
  - Total pattern is R0^d ++ [R1; R0]
  - Parameters (d,n) are unique

### Necessary Conditions
- The evenness of m forces pattern to be R0R0, not R1R0
- The oddness of n (and thus output) forces next operations to be R1 then R0
- The requirement is_odd n is necessary for canonical representation

## Technical Features

### Proof Strategy

1. **Case Analysis**: Use build_k_steps_numeric_canonical to split into R1R0/R0R0 cases
2. **R1R0 Case** (impossible):
   - Contradiction: R0R0 entry is even, but R1R0 entry would be odd
3. **R0R0 Case** (main branch):
   - Use uniqueness to confirm we're in R0R0 branch
   - Define Send = output of R0 sequence
   - Prove Send = n using R0R0_output_exact_n
   - Prove Send is odd using is_odd n
   - Show build_k_steps m (S d) = R0^d ++ [R1; R0] using build_k_steps_Sn
   - Prove uniqueness of parameters using R0R0_decomposition_unique

### Code Structure
```coq
Proof.
  intros m d n Hm Hd Hn Hodd Hrepr.
  pose proof (build_k_steps_numeric_canonical m Hm) as Hcanonical.
  destruct Hcanonical as [[d0 [...]] | [d0 [...]]].
  - // R1R0 case - contradiction
    exfalso.
    // R0R0 entry is even, R1R0 would be odd - impossible
  - // R0R0 case
    pose proof (Hunique1 d n ...) as [Hd_eq Hn_eq].
    subst d0 n0.
    set (Send := sequence_end m (repeat_R0 d)).
    assert (Hsend_eq : Send = n).
    // ... prove all properties
Qed.
```

### Key Technical Points

1. **Uniqueness Application**: Hunique1 shows no other (d',n') with odd n' works
2. **Parity Proof**: Oddness of R0 output is critical (output = n, and is_odd n)
3. **Pattern Extension**: build_k_steps_Sn extends pattern by one step (R1 then R0)
4. **Contradiction**: R1R0 and R0R0 entries are disjoint (odd vs even)

## Applications and Significance

### Theoretical Significance
1. **Pattern Determinism**: Shows Collatz operations are deterministic at canonical level
2. **Alternating Structure**: Completes the R1R0 ↔ R0 alternation with R0 ↔ R1R0
3. **Canonical Steps**: Defines "canonical step" from both odd and even perspectives

### Practical Applications
1. **Sequence Construction**: Builds complete Collatz sequences from alternating patterns
2. **Pattern Recognition**: Identifies canonical steps of both types in sequences
3. **Uniqueness**: Ensures unique decomposition of sequences into canonical steps

## Example Explanations

### Example 1: m=6, d=1, n=3
- Starting: 6 = valid_R0R0_entry_number 1 3 = 3 * 2^1 ✓
- n=3 is odd ✓
- R0 phase: 6 → 3
- Output: Send = 3 ✓ (odd!)
- Extended pattern: build_k_steps 6 2 = [R0; R1; R0]
- Verification: 6 → 3 (R0) → 10 → 5 (R1R0)

### Example 2: m=12, d=2, n=3
- Starting: 12 = valid_R0R0_entry_number 2 3 = 3 * 2^2 ✓
- n=3 is odd ✓
- R0 phase: 12 → 6 → 3
- Output: Send = 3 ✓ (odd!)
- Extended pattern: build_k_steps 12 3 = [R0; R0; R1; R0]
- Verification: 12 → 6 → 3 (R0^2) → 10 → 5 (R1R0)

### Example 3: m=20, d=2, n=5
- Starting: 20 = valid_R0R0_entry_number 2 5 = 5 * 2^2 ✓
- n=5 is odd ✓
- R0 phase: 20 → 10 → 5
- Output: Send = 5 ✓ (odd!)
- Extended pattern: build_k_steps 20 3 = [R0; R0; R1; R0]
- Verification: 20 → 10 → 5 (R0^2) → 16 → 8 (R1R0)

### Example 4: m=56, d=3, n=7
- Starting: 56 = valid_R0R0_entry_number 3 7 = 7 * 2^3 ✓
- n=7 is odd ✓
- R0 phase: 56 → 28 → 14 → 7
- Output: Send = 7 ✓ (odd!)
- Extended pattern: build_k_steps 56 4 = [R0; R0; R0; R1; R0]
- Verification: 56 → 28 → 14 → 7 (R0^3) → 22 → 11 (R1R0)

## Related Theorems

- **odd_leads_R1R0_then_R0_pattern**: Complementary theorem for odd numbers
- **build_k_steps_numeric_canonical**: Source of canonical representation
- **R0R0_decomposition_unique**: Proves uniqueness with odd n requirement
- **collatz_pattern_cycle_deterministic**: Global deterministic cycle pattern

## Historical Context

This theorem completes the **alternating pattern** structure:
- Odd numbers → R1R0 → Even → R0 (single operation)
- Even numbers → R0^d → Odd → R1R0 (pair of operations)

Together with odd_leads_R1R0_then_R0_pattern, this shows:
1. **Deterministic Cycles**: Patterns alternate deterministically
2. **Cycle Types**: Two types of cycles (R1R0→R0 and R0→R1R0)
3. **Canonical Steps**: Each "step" in canonical sense is either R1R0^d + [R0] or R0^d + [R1; R0]

## Connection to Overall Collatz Dynamics

These two theorems reveal fundamental structure:

### Alternating Patterns

```
Odd m:
  m --R1R0^d--> Send (even)
  Send --R0--> Next (odd)
  Next --R1R0--> ...

Even m:
  m --R0^d--> Send (odd)
  Send --R1--> T (even)
  T --R0--> Next (odd)
  Next --R1R0--> ...
```

### Key Insights

1. **Determinism**: At canonical level, Collatz is completely deterministic
2. **Cycle Structure**: Patterns form deterministic cycles
3. **Balance**: R1R0 (growing) and R0 (shrinking) alternate
4. **Parity Control**: Parity of numbers forces operation choices

This structure is essential for understanding global behavior and proving convergence properties.

## Combined Impact with Odd Theorem

Together, odd_leads_R1R0_then_R0_pattern and even_leads_R0_then_R1R0_pattern provide:
1. **Complete Coverage**: All positive integers m ≥ 1 are covered
2. **Deterministic Next Operation**: The next operation is uniquely determined by canonical form
3. **Canonical Step Definition**: Defines what constitutes a "canonical step" from either perspective
4. **Global Cycle Pattern**: Establishes that Collatz sequences follow deterministic alternating patterns

This is a major milestone in understanding Collatz sequence structure at the canonical level.
