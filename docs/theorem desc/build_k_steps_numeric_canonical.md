# build_k_steps_numeric_canonical - Unique Canonical Representation Theorem

## Basic Information

- **Theorem Type**: Theorem
- **Location**: collatz_part_14.v:130-195
- **Description**: Every positive integer m uniquely corresponds to canonical representation of R1R0 or R0R0 branch with determined bounds

## Theorem Statement

```coq
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
```

## Theorem Purpose

This theorem establishes **uniqueness** of canonical representations:
1. **R1R0 Branch**: Unique (d,n) with strict upper bound and uniqueness property
2. **R0R0 Branch**: Unique (d,n) with canonical odd factorization and uniqueness

Key innovation: Adds **uniqueness quantification** to the existence theorem.

## Theorem Properties

### Mathematical Properties
- **Uniqueness**: For each m, there is exactly one representation in each branch
- **Canonical Forms**: Both branches provide canonical forms
- **R1R0 Strictness**: Introduces strict upper bound S < 2*3^d*(n+1)
- **R0R0 Odd Factorization**: Requires n to be odd (canonical factor)

### Key Differences from Previous Theorems

| Property | build_k_steps_numeric_bounds_exists | build_k_steps_numeric_canonical |
|----------|----------------------------------|-------------------------------|
| Type | Existence | Existence + Uniqueness |
| R1R0 Upper Bound | ≤ (non-strict) | < (strict) |
| R0R0 Requirement | n ≥ 1 | n ≥ 1 + is_odd n |
| Uniqueness | Not proved | Explicitly proved |

## Technical Support

### Direct Dependencies

**R1R0 Branch**:
1. **build_k_steps_numeric_bounds_exists**: Provides existence and basic bounds
2. **tighten_R1R0_strict_upper**: Converts ≤ to < (strict upper bound)
3. **R1R0_decomposition_unique**: Proves uniqueness of (d,n) representation

**R0R0 Branch**:
1. **build_k_steps_numeric_bounds_exists**: Provides existence
2. **R0R0_canonical_factorization**: Finds canonical odd factorization
3. **R0R0_branch_simplification**: Simplifies to canonical form
4. **R0R0_decomposition_unique**: Proves uniqueness

## Sufficient and Necessary Support

### Sufficient Conditions
- Any m ≥ 1 has a unique canonical representation

### Necessary Conditions (from uniqueness)
- The parameters (d,n) must be unique
- For R0R0, n must be odd (canonical factorization)

## Technical Features

### Proof Strategy

**R1R0 Branch**:
1. Use build_k_steps_numeric_bounds_exists for existence
2. Apply tighten_R1R0_strict_upper for strict bound
3. Apply R1R0_decomposition_unique for uniqueness

**R0R0 Branch**:
1. Use build_k_steps_numeric_bounds_exists for existence
2. Apply R0R0_canonical_factorization to find canonical (dc, nc)
3. Apply R0R0_branch_simplification to show equivalence
4. Apply R0R0_decomposition_unique for uniqueness

### Key Innovations

1. **Strict Upper Bound** (R1R0):
   - Previous: S ≤ 3^d*(2n+1)
   - Now: S < 2*3^d*(n+1)
   - Both bounds hold and are tighter

2. **Canonical Odd Factorization** (R0R0):
   - Requires is_odd n
   - Ensures unique decomposition
   - Removes redundancy from even factors

## Applications and Significance

### Theoretical Significance
1. **Uniqueness**: Canonical forms are unique for each integer
2. **Classification**: Provides definitive classification theorem
3. **Canonicalization**: Shows how to find canonical representations

### Practical Applications
1. **Pattern Matching**: Uniquely determine pattern type for any number
2. **Canonical Forms**: Use canonical forms in algorithms
3. **Decomposition**: Unique factorization into operations

## Example Explanations

### Example 1: m=7 (R1R0 branch)
- Unique representation: d=1, n=1
- Valid: 7 = valid_R1R0_entry_number 1 1 ✓
- Pattern: [R1; R0]
- Bounds: 6 ≤ 8 < 12, 2 ≤ 8 ✓
- Uniqueness: No other (d',n') works

### Example 2: m=12 (R0R0 branch)
- Non-canonical: 12 = valid_R0R0_entry_number 2 3, but 3 is odd ✓
- Pattern: [R0; R0]
- Output: 3 = n ✓
- Uniqueness: No other (d',n') with odd n' works

### Example 3: m=24
- Non-canonical: 24 = valid_R0R0_entry_number 3 3 (n=3 is odd ✓)
- Canonical: d=3, n=3 (unique)
- Pattern: [R0; R0; R0]
- Output: 3 = n ✓

## Related Theorems

- **build_k_steps_numeric_bounds_exists**: Existence without uniqueness
- **R1R0_decomposition_unique**: R1R0 uniqueness lemma
- **R0R0_decomposition_unique**: R0R0 uniqueness lemma
- **R0R0_canonical_factorization**: Canonical factorization lemma

## Historical Context

This theorem represents the **canonicalization** phase:
1. Phase 1: Existence (build_k_steps_numeric_bounds_exists)
2. Phase 2: Uniqueness + Canonicalization (this theorem)

The addition of uniqueness transforms the representation from "some representation" to "the canonical representation."

## Connection to Overall Formalization

This theorem is crucial for:
- **Definitive Classification**: Provides definitive answer to "what pattern does this number follow?"
- **Canonical Forms**: Establishes canonical forms used throughout the formalization
- **Uniqueness Proofs**: Foundation for reasoning about uniqueness in more complex contexts

The theorem ensures that every integer has a single, well-defined canonical representation, which is essential for rigorous analysis.
