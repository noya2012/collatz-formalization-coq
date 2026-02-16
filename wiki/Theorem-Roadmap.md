# Theorem Roadmap - Dependency Chain

## Six-Phase Architecture

```
Phase 1          Phase 2          Phase 3          Phase 4          Phase 5          Phase 6
Foundations  →   Classification   Pattern Analysis  Conversion   →   Advantage    →   Global
                 & Parametrization                  Mechanism        Theory            Growth
```

---

## Phase 1: Foundations (collatz_part_1 - 5)

### Core Definitions

| Definition | Description |
|------------|-------------|
| `CollatzOp` | R0 and R1 operation types |
| `collatz_step` | Single Collatz step function |
| `valid_sequence` | Sequence validity predicate |
| `sequence_end` | Final value after sequence execution |

### Key Achievement

Machine-checkable foundation for all subsequent proofs.

---

## Phase 2: Classification (collatz_part_3)

### Entry Functions

```
valid_R1R0_entry_number(d, n) = 2·2^d·n + (2^d - 1)  [odd entries]
valid_R0R0_entry_number(d, n) = n·2^d                [even entries]
```

### Core Theorem

**`complete_number_classification`**

```
∀ m ≥ 1: m is odd  → ∃ d,n: m = valid_R1R0_entry_number(d,n)
           m is even → ∃ d,n: m = valid_R0R0_entry_number(d,n)
```

### Significance

Maps chaotic integer space to structured (d, n) parameters.

---

## Phase 3: Pattern Analysis (collatz_part_10 - 14)

### R1R0 Pattern Theorems

| Theorem | Result |
|---------|--------|
| `repeat_R1R0_output_closed_form_no_div` | Output = 2·3^D·n + (3^D - 1) |
| `R1R0_bounds_summary` | Triple bounds on output |
| `R1R0_power_iff` | Power-of-2 ↔ Diophantine equation |

### R0R0 Pattern Theorems

| Theorem | Result |
|---------|--------|
| `R0R0_bounds_summary` | Output = n exactly |
| `build_k_steps_numeric_canonical` | Unique canonical representation |

### Key Achievement

Closed-form algebraic expressions replace dynamic analysis.

---

## Phase 4: Conversion Mechanism (collatz_part_16)

### Pattern Transformation

| Theorem | Transformation |
|---------|----------------|
| `odd_leads_R1R0_then_R0_pattern` | Odd entry → R1R0 → even output |
| `even_leads_R0_then_R1R0_pattern` | Even entry → R0 → odd output |

### State Machine

```
        ┌─────────────────────────────────────┐
        │                                     │
        ▼                                     │
    Odd Entry ──[R1R0^d]──► Even Output ──┐   │
        ▲                                 │   │
        │                                 ▼   │
        └─── Odd Output ◄──[R0^d]── Even Entry
```

### Key Achievement

Deterministic interface between branches.

---

## Phase 5: Advantage Theory (collatz_part_17 - 18)

### Canonical Chain Advantage

**`canonical_chain_R0_advantage`**

```
R0 advantage of canonical_chain(true, d)  = 1
R0 advantage of canonical_chain(false, d) = d
```

### Concatenation Theorem

**`generalized_concatenated_chains_R0_advantage`**

```
advantage(chain1 ++ chain2) = advantage(chain1) + advantage(chain2)
```

### Universal Bounds

**`universal_R0_advantage_bounds`**

| Chain Type | R0 Count | R1 Count | Advantage |
|------------|----------|----------|-----------|
| R1R0 (d) | d + 1 | d | 1 |
| R0R0 (d) | d + 1 | 1 | d |

### Key Achievement

Composable counting framework for R0 advantage.

---

## Phase 6: Global Growth (collatz_part_19)

### Mod 6 ≡ 2 Orbit Entry

**`direct_conversion_to_mod6_2_orbit_canonical`**

```
∀ m: ∃ k ≤ 2·(log₂ m + 1): sequence reaches mod 6 ≡ 2
```

### Single Macrostep

**`mod62_R0advantage_canonical`**

```
Macrostep from mod 6 ≡ 2: advantage = d₀ + 1 ≥ 2
```

### Iterated Macrosteps

**`mod62_macrostep_iterated_lower_bound_canonical`**

```
After t macrosteps: advantage ≥ 2t
```

### Global Theorem

**`global_mod62_advantage_growth_canonical`**

```
∀ m ≥ 1, t ≥ 1: ∃ construction with:
  - k ≤ 2·(log₂ m + 1) operations to reach mod 6 ≡ 2
  - t macrosteps, each contributing ≥ 2 to advantage
  - Total advantage ≥ 2t
```

### Key Achievement

Universal linear growth of R0 advantage.

> 🔬 **[Interactive Visualization](cz_ms_cc_visualization)**: Visualize macrosteps, chain records, and R0 advantage on real Collatz sequences

---

## Dependency Summary

```
complete_number_classification
         │
         ▼
build_k_steps_pattern_completeness
         │
         ▼
R1R0_bounds_summary / R0R0_bounds_summary
         │
         ▼
build_k_steps_numeric_canonical
         │
         ▼
odd_leads_R1R0_then_R0_pattern
even_leads_R0_then_R1R0_pattern
         │
         ▼
canonical_chain_R0_advantage
         │
         ▼
generalized_concatenated_chains_R0_advantage
         │
         ▼
direct_conversion_to_mod6_2_orbit_canonical
         │
         ▼
mod62_macrostep_iterated_lower_bound_canonical
         │
         ▼
global_mod62_advantage_growth_canonical
```

---

## Statistics

| Metric | Value |
|--------|-------|
| Total Theorems | 19 |
| Total Corollaries | 4 |
| Intermediate Results | 143 |
| Max Dependency Depth | 17 |
| Proof Files | 24 |

---

## Theorem Index

| # | Theorem | Phase | Location |
|---|---------|-------|----------|
| 1 | complete_number_classification | 2 | collatz_part_3.v |
| 2 | build_k_steps_pattern_completeness | 3 | collatz_part_11.v |
| 3 | R1R0_bounds_summary | 3 | collatz_part_11.v |
| 4 | R1R0_power_iff | 3 | collatz_part_11.v |
| 5 | R0R0_bounds_summary | 3 | collatz_part_12.v |
| 6 | build_k_steps_numeric_canonical | 3 | collatz_part_14.v |
| 7 | odd_leads_R1R0_then_R0_pattern | 4 | collatz_part_16.v |
| 8 | even_leads_R0_then_R1R0_pattern | 4 | collatz_part_16.v |
| 9 | canonical_chain_R0_advantage | 5 | collatz_part_17.v |
| 10 | generalized_concatenated_chains_R0_advantage | 5 | collatz_part_17.v |
| 11 | generalized_valid_chains_sequence_R0_advantage | 5 | collatz_part_17.v |
| 12 | universal_R0_advantage_bounds | 5 | collatz_part_18.v |
| 13 | direct_conversion_to_mod6_2_orbit_canonical | 6 | collatz_part_19.v |
| 14 | mod62_R0advantage_canonical | 6 | collatz_part_19.v |
| 15 | mod62_macrostep_iterated_lower_bound_canonical | 6 | collatz_part_19.v |
| 16 | global_mod62_advantage_growth_canonical | 6 | collatz_part_19.v |
