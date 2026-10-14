# Sharp continued-fraction bounds from exact digit runs

This project proves sharp bounds for the minimum and maximum of three
consecutive ordinary continued-fraction approximation coefficients,
including actual irrational extremizing sequences and an optimal global
linear inverse estimate.

Fix an integer central partial quotient $a\ge2$. Specify exactly $r$
adjacent copies of $a$ in the past and $s$ in the future, followed on
each side by a digit less than or greater than $a$. Four rational corner
evaluations give the sharp constants for both objectives, for every
$r,s\ge0$. Actual irrational triples satisfy strict inequalities and
approach both bounds within their prescribed classes. This sharpness
allows the finite index to vary.

The package also proves:

- Exact clipping formulas and all equality cases on every closed
  rectangle in the unit square, for real $a\ge1$, including axes,
  line segments, and singletons.
- Strict sharp bounds with an entire nonempty finite digit word fixed,
  preserving that word and its fixed index in the approaching sequences.
- The exhausted-past and infinite constant-future boundary cases,
  genuine attained boundary examples, and exact alternating formulas
  for the fully constant input.
- Effective convergence of all run constants and a quantitative deficit
  condition forcing an actual constant-digit window on both sides.

For $\beta=(\sqrt{a^2+4}-a)/2$, $c=1/\sqrt{a^2+4}$, and
$F_a(x,y)=\min\{1,x(a+y),y(a+x)\}/(a+x+y)$, the inverse estimate is

```math
c-F_a(x,y)\ge
\frac{c(a+1-\beta)}{1+(a+1)^2}
\max\{|x-\beta|,|y-\beta|\},\qquad x,y\in[0,1].
```

The coefficient is best possible for every real $a\ge2$. Equality holds
exactly at $(\beta,\beta)$, $(1,1/(a+1))$, and its transpose. For integer
$a\ge2$, the coefficient remains optimal over actual ordinary convergent
triples, although none attains equality. At $a=2$ it is
$(2\sqrt2-1)/20$.

For immediate departures on either side of the silver digit $2$:

| Departing digits | Sharp upper bound for the minimum | Sharp lower bound for the maximum |
| --- | --- | --- |
| $1,1$ | $1/3$ | $5/12$ |
| $1,\ge3$ or reversed | $3/10$ | $2/5$ |
| $\ge3,\ge3$ | $7/24$ | $3/8$ |

The formal statements use Mathlib's ordinary convergents of the input
real number and its actual floor/fraction digits. Their error identities
are proved from these definitions. Both the written account and Lean
index the triple as $n,n+1,n+2$, with central digit $n+2$.

[Challenge.lean](Challenge.lean) gives the inspectable definitions and
statements. [Solution.lean](Solution.lean) exports their proofs.
[Proof.md](Proof.md) develops the mathematics and boundary conventions;
[Applications.md](Applications.md) gives the quantitative consequences.
[Sources.md](Sources.md) credits the classical results, related geometry,
and the explicit extension suggestion of Adhin, Bakhtawar and Kraaikamp.
[Verification.md](Verification.md) records formal coverage and reproducible
checks, and [Disclosure.md](Disclosure.md) records automated assistance.

Build with the pinned Lean toolchain:

```bash
lake exe cache get
lake build
python3 scripts/audit_axioms.py
python3 scripts/check_negative_controls.py
```

The project does not assert worldwide priority, independent human
specialist peer review, or a classification of a Markov or Lagrange spectrum.
