# Sharp continued-fraction bounds from exact digit runs

This project proves sharp bounds for the minimum and maximum of three
consecutive ordinary continued-fraction approximation coefficients. It also
proves an optimal global linear inverse estimate and applies it to actual
irrational inputs.

Fix a central partial quotient $a\ge2$. Specify exactly $r$ adjacent
copies of $a$ in the past and $s$ in the future, followed on each side
by a digit less than or greater than $a$. Four rational corner evaluations
give the sharp constants for both objectives, for every $r,s\ge0$.
Actual irrational inputs satisfy strict inequalities; admissible inputs
approach both bounds. The approximating finite index may vary.

With $\beta=(\sqrt{a^2+4}-a)/2$, $c=1/\sqrt{a^2+4}$, and
$F_a(x,y)=\min\{1,x(a+y),y(a+x)\}/(a+x+y)$, the global inverse estimate is

```math
c-F_a(x,y)\ge
\frac{c(a+1-\beta)}{1+(a+1)^2}
\max\{|x-\beta|,|y-\beta|\},\qquad x,y\in[0,1].
```

The coefficient is best possible for every real $a\ge2$. Equality holds
exactly at $(\beta,\beta)$, $(1,1/(a+1))$, and its transpose. For integer
$a\ge2$, the same coefficient is optimal over actual ordinary convergent
triples, although none attains equality. At $a=2$ the coefficient is
$(2\sqrt2-1)/20$.

For immediate departures on either side of the silver digit $2$:

| Departing digits | Sharp upper bound for the minimum | Sharp lower bound for the maximum |
| --- | --- | --- |
| $1,1$ | $1/3$ | $5/12$ |
| $1,\ge3$ or reversed | $3/10$ | $2/5$ |
| $\ge3,\ge3$ | $7/24$ | $3/8$ |

The formal statements use Mathlib's ordinary convergents of the input
real number and its floor/fraction digit algorithm. The error identities
are proved from those definitions. In Lean, the triple is indexed
$n,n+1,n+2$ for $n\ge0$, with central digit $n+2$.

- [Challenge.lean](Challenge.lean) gives the inspectable definitions and statements.
- [Solution.lean](Solution.lean) exports the proofs in [ContinuedFractionBounds](ContinuedFractionBounds).
- [Proof.md](Proof.md) gives the mathematical account and boundary distinctions.
- [Applications.md](Applications.md) gives localization, digit-window and cylinder consequences.
- [Sources.md](Sources.md) credits the classical results and the explicit extension suggestion of Adhin, Bakhtawar and Kraaikamp.
- [Verification.md](Verification.md) identifies formal coverage and reproducible checks.
- [Disclosure.md](Disclosure.md) records authorship and automated assistance.

Build with the pinned Lean toolchain:

```bash
lake exe cache get
lake build
python3 scripts/audit_axioms.py
python3 scripts/check_negative_controls.py
```

The project does not claim worldwide priority, external specialist peer
review, or a classification of a Markov or Lagrange spectrum.
