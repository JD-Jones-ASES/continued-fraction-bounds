# Sharp continued-fraction bounds from exact digit runs

Let $\alpha=[a_0;a_1,a_2,\ldots]$ be irrational, and let $p_i/q_i$ be
its ordinary simple continued-fraction convergents. Write
$\Theta_i=q_i|q_i\alpha-p_i|$. Fix $n\ge1$ and $a_{n+1}=a\ge2$.
The finite past and infinite future coordinates are

```math
x=[0;a_n,\ldots,a_1]=q_{n-1}/q_n,
\qquad y=[0;a_{n+2},a_{n+3},\ldots].
```

Thus $x\in\mathbb Q\cap(0,1]$ and $y\in(0,1)\setminus\mathbb Q$.
In particular, $x=1$ is allowed. Define

```math
T_a(t)=\frac1{a+t},\quad
\beta_a=\frac{\sqrt{a^2+4}-a}{2},\quad
c_a=\frac1{\sqrt{a^2+4}},
```

and

```math
F_a(x,y)=\frac{\min\{1,x(a+y),y(a+x)\}}{a+x+y},\qquad
G_a(x,y)=\frac{\max\{1,x(a+y),y(a+x)\}}{a+x+y}.
```

The classical metallic thresholds are prior results. The contributions
considered here are the exact-run refinement of both envelopes, the sharp
linear inverse estimate, and their cylinder applications. [Sources](Sources.md)
describes the relationship to the literature; priority is not asserted.

## Ordinary convergents and the coordinate formulas

Use $p_{-1}=1,q_{-1}=0,p_0=a_0,q_0=1$. The ordinary continuant
recurrences and determinant identity give

```math
p_{i+1}=a_{i+1}p_i+p_{i-1},\quad
q_{i+1}=a_{i+1}q_i+q_{i-1},\quad
p_iq_{i-1}-p_{i-1}q_i=(-1)^{i-1}.
```

The complete quotient at position $n+1$ is $a+y$, so

```math
\alpha=\frac{p_n(a+y)+p_{n-1}}{q_n(a+y)+q_{n-1}}.
```

Subtracting the three consecutive convergents, taking absolute values,
and using the determinant identity yields

```math
(\Theta_{n-1},\Theta_n,\Theta_{n+1})
=\frac{(x(a+y),1,y(a+x))}{a+x+y}.                       \tag{1}
```

Consequently their minimum is $F_a(x,y)$ and their maximum is $G_a(x,y)$.
These identities refer to the actual convergents of $\alpha$. An arbitrary
unimodular pair bracketing $\alpha$, with an arbitrarily assigned next
digit, need not satisfy the required error recurrence.

## Exact optimization on a rectangle

For this section it is enough that $a\ge1$ is real. Put
$R=[\ell_x,u_x]\times[\ell_y,u_y]\subseteq[0,1]^2$, and

```math
Q(x,y)=\min\{x(a+y),y(a+x)\},\quad
P(x,y)=\max\{x(a+y),y(a+x)\}.
```

Let $\operatorname{clip}(z;L,U)=\min\{U,\max\{L,z\}\}$.
For $t>0$, set

```math
h(t)=\max\{1/t-a,1/(a+t)\},\quad
k(t)=\max\{0,\min\{1/t-a,1/(a+t)\}\},\quad k(0)=1/a.
```

The maximum of $F_a$ on $R$ is computed as follows.

1. If $u_xu_y=0$, the function is identically zero on $R$.
2. Otherwise, if $Q(u_x,u_y)\le1$, its unique maximizer is $(u_x,u_y)$.
3. Otherwise, if $Q(\ell_x,\ell_y)\ge1$, its unique maximizer is
   $(\ell_x,\ell_y)$.
4. In the remaining case let
   $L=\max\{\ell_x,h(u_y)\}$ and $U=\min\{u_x,h(\ell_y)\}$.
   If $\ell_y=0$, use $U=u_x$. Then $0<L\le U\le1$, and the unique
   maximizer is $(x_*,h(x_*))$ for $x_*=\operatorname{clip}(\beta_a;L,U)$.

The minimum of $G_a$ is always unique. If $P(u_x,u_y)\le1$, its
minimizer is $(u_x,u_y)$; otherwise, if $P(\ell_x,\ell_y)\ge1$, it is
$(\ell_x,\ell_y)$. In the remaining case put

```math
L=\max\{\ell_x,k(u_y)\},\quad U=\min\{u_x,k(\ell_y)\}.
```

Then $0\le L\le U\le1/a$, and the minimizer is
$(x_*,k(x_*))$, where $x_*=\operatorname{clip}(\beta_a;L,U)$.
At either crossing-curve extremizer the objective equals $1/(a+x_*+y_*)$.

To prove the formulas, note that the two side fractions in (1) increase
strictly in either positive coordinate, while the central fraction decreases.
For example, their relevant difference quotients have the same signs as
$(a+y)^2$ and $x^2$, with positive denominators. Thus any positive
maximizer of $F_a$ in the crossing case lies on $Q=1$. This curve is
$y=h(x)$: its branches are $1/x-a$ below $\beta_a$ and $1/(a+x)$ above
$\beta_a$. The function $h$ is a decreasing involution on positive reals.
Along the curve, $x+h(x)$ strictly decreases up to $\beta_a$ and strictly
increases afterwards. This proves the clipping formula and uniqueness.
Axis points have value zero and cannot maximize a rectangle with positive
upper coordinates.

For $G_a$, move toward the appropriate corner until reaching $P=1$.
This curve is $y=k(x)$ for $0\le x\le1/a$, a decreasing involution on
that interval. Along it, $x+k(x)$ strictly increases up to $\beta_a$ and
strictly decreases afterwards. Minimizing $1/(a+x+k(x))$ therefore gives
the same clipping rule. The monotonicity extends to the axes: above
$P=1$ the active side coefficient has positive variation in either
coordinate. Degenerate rectangles obey the same statements.

Taking $R=[0,1]^2$ proves

```math
F_a(x,y)\le c_a\le G_a(x,y),
```

with equality in either inequality exactly at $(\beta_a,\beta_a)$.

## Four corners for every exact run

For an integer $a\ge2$ and natural $r$, define sorted image intervals

```math
I_r^L=T_a^r([1/a,1]),\qquad I_r^H=T_a^r([0,1/(a+1)]).
```

The superscript $L$ means that the first departing digit is less than
$a$; $H$ means it is greater. For $R=I_r^e\times I_s^f$, let $V(R)$
be its four corners. Define

```math
C_{a;r,s}^{e,f}=\max_{v\in V(R)}F_a(v),\qquad
U_{a;r,s}^{e,f}=\min_{v\in V(R)}G_a(v).                  \tag{2}
```

Both constants are rational. Each is the corresponding extremum over
the whole rectangle and has a unique extremizing corner. Furthermore,

```math
C_{a;r,s}^{e,f}<c_a<U_{a;r,s}^{e,f}.                    \tag{3}
```

Here is the structural proof, which has no cutoff on $r$ or $s$.
Let $K_r=T_a^r([0,1])$. These intervals are nested, and

```math
K_r\setminus\operatorname{int}(K_{r+1})=I_r^L\cup I_r^H.
```

The map $T_a^r$ is strictly monotone. Distinct run cells therefore meet
only at shared endpoints; every cell excludes $\beta_a$, which lies in
the interior of every $K_r$. Also $T_a(I_s^f)=I_{s+1}^f$.

The rectangle formulas place an extremum at a corner unless it lies on
one of the curves $x=T_a(y)$ or $y=T_a(x)$. On the first curve, its
possible first coordinates lie in $I_r^e\cap I_{s+1}^f$. If these cells
differ, every intersection is a shared endpoint and the point is a
corner. If they coincide, the curve joins opposite corners. It lies
strictly on one side of the metallic point, so the relevant objective
is strictly monotone along it and its extremum is an endpoint. Exchange
the coordinates to treat the second curve. Uniqueness and (3) follow
from the rectangle theorem.

For exact computation set $P_{-1}=1,P_0=0$ and
$P_{j+1}=aP_j+P_{j-1}$. Induction gives

```math
T_a^r(t)=\frac{P_{r-1}t+P_r}{P_rt+P_{r+1}}.             \tag{4}
```

Evaluate (4) at $0,1/(a+1),1/a,1$, sort the endpoint pairs, and perform
the four evaluations in (2). For a central digit $2$ with immediate
departures, the resulting constants are:

| Departure digits | $C$ | $U$ |
| --- | --- | --- |
| $1,1$ | $1/3$ | $5/12$ |
| $1,\ge3$, or reversed | $3/10$ | $2/5$ |
| $\ge3,\ge3$ | $7/24$ | $3/8$ |

## Realization, strictness, and sharpness

Before applying $T_a^r$, the possible finite past coordinates are
$\mathbb Q\cap[1/a,1]$ for type $L$ and
$\mathbb Q\cap(0,1/(a+1)]$ for type $H$. The possible infinite future
coordinates are exactly the irrational points in the corresponding
open intervals. The endpoint $1/a$ belongs to the low-departure finite
past class through $[0;a-1,1]$. Requiring a canonical reversed finite
expansion would incorrectly remove it.

Every interior rational has a finite positive-digit expansion. Reversing
its digit word gives an ordinary finite past. Every interior irrational
has an infinite positive-digit expansion. The past and future words
can be chosen independently on opposite sides of the central digit.
The fractional-linear reconstruction used in (1) combines them into an
actual irrational input. Rationals and irrationals are dense in their
respective intervals, and these fractional-linear maps are continuous.

It follows that every actual triple in a terminated run class satisfies

```math
\min(\Theta_{n-1},\Theta_n,\Theta_{n+1})
 < C_{a;r,s}^{e,f}<c_a<U_{a;r,s}^{e,f}
 <\max(\Theta_{n-1},\Theta_n,\Theta_{n+1}).               \tag{5}
```

The first constant is the exact supremum, and the second the exact
infimum. For every positive $\epsilon$, there is an actual triple in
the same class within $\epsilon$ of either bound. The two approaching
sequences need not be the same. The finite index may vary. This is not
optimality for an independently prescribed index.

Strictness follows because each unique extremizing corner has rational
future coordinate, while an actual infinite future is irrational.
Density and continuity prove sharpness. More generally, finite digit
words produce rational-endpoint cylinders, to which the full rectangle
formulas apply. Four corners alone do not optimize arbitrary rectangles.

## Sharp global linear inverse stability

For every real $a\ge2$, put

```math
\kappa_a=\frac{c_a(a+1-\beta_a)}{1+(a+1)^2}.
```

On the entire unit square,

```math
c_a-F_a(x,y)\ge\kappa_a
   \max\{|x-\beta_a|,|y-\beta_a|\}.                    \tag{6}
```

The coefficient is positive and largest possible. Equality holds exactly at

```math
(\beta_a,\beta_a),\quad (1,1/(a+1)),\quad(1/(a+1),1).
```

For $a=2$, it equals $(2\sqrt2-1)/20$.

One proof optimizes the second coordinate. With $b=a+1,d=1/b$,

```math
J(t):=\max_{0\le u\le1}F_a(t,u)=
\begin{cases}
bt/(b+t),&0\le t\le d,\\
t/(1+t^2),&d\le t\le\beta_a,\\
(a+t)/(1+(a+t)^2),&\beta_a\le t\le1.
\end{cases}
```

The maximizing second coordinate, for $t>0$, is respectively $1$,
$1/t-a$, or $1/(a+t)$. The first two branches form an increasing
concave function. Their slopes at the join decrease, and the final
left derivative is $B=(1-\beta_a^2)/(1+\beta_a^2)^2$. Hence

```math
\frac{c_a-J(t)}{\beta_a-t}\ge B\quad (t<\beta_a).
```

For $t>\beta_a$, set $\gamma=a+\beta_a=1/\beta_a$ and $z=a+t$.
Then

```math
\frac{c_a-J(t)}{t-\beta_a}
=\frac{\gamma z-1}{(1+\gamma^2)(1+z^2)}=:R(z).
```

This decreases strictly for $z\ge\gamma$: its derivative has numerator
$\gamma(1-z^2)+2z$, which is negative there since
$\gamma\ge1+\sqrt2>\sqrt3$. Thus $R(z)\ge R(a+1)=\kappa_a$,
with equality precisely when $t=1$. Also
$0<\kappa_a<R(\gamma)=\beta_a^2B<B$.

Choose the coordinate realizing the maximum distance from $\beta_a$.
The corresponding secant estimate proves (6). Equality away from the
metallic point forces that coordinate to be $1$ and the other to be
its unique optimizer $1/(a+1)$. These equality points prove optimality.

There is also a purely algebraic proof: compare $F_a(t,u)$ to
$t/(1+t^2)$ and $(a+t)/(1+(a+t)^2)$ by splitting at the two switching
curves, then clear positive denominators in the corresponding secant
inequalities. This avoids differentiation without changing the statement.

For integer $a\ge2$, equality is impossible for an actual triple: the
metallic past is irrational, and the other equality points have rational
future. Nevertheless the coefficient remains optimal for actual triples.
Take $[0;1,a,a+1,N,\overline2]$ at index $n=1$. Its past is $1$, and
its irrational future tends to $1/(a+1)$ as $N\to\infty$. The ratio
of deficit to distance tends to $\kappa_a$ by continuity.

## Boundary cases

If the entire finite past is fixed, use the singleton first interval in
the rectangle theorem. For positive rational past and rational-endpoint
future cylinder, the unique optimizing future is rational, so both
actual inequalities remain strict and sharp.

An exhausted all-$a$ past is $x=T_a^n(0)$. An infinite all-$a$ future is
$y=\beta_a$. In the latter case, both extrema over a terminated past
cell occur at its endpoint nearest $\beta_a$, and equality can be
attained. For type $L$, the endpoint is $T_a^r(1/a)$, realized by
$[0;1,a-1,\overline a]$ at index $n=r+2$. For type $H$, it is
$T_a^r(1/(a+1))$, realized by $[0;a+1,\overline a]$ at $n=r+1$.
These observations distinguish an infinite constant future from a
terminated future.

For $[a_0;\overline a]$, the individual coefficients are

```math
\Theta_k=c_a\bigl(1-(-1)^{k+1}\beta_a^{2k+2}\bigr),\qquad k\ge0.
```

The three-term minimum, for $n\ge1$, is $c_a(1-\beta_a^{2n+2})$
when $n$ is odd and $c_a(1-\beta_a^{2n})$ when $n$ is even. The
maximum is $c_a(1+\beta_a^{2n})$ for odd $n$ and
$c_a(1+\beta_a^{2n+2})$ for even $n$. Thus finite-index inequalities
are strict and both bounds tend to the metallic threshold.
The optional empty past $n=0$ has $\Theta_{-1}=0$ and is excluded
from (5).

The applications and explicit quantitative estimates are in
[Applications.md](Applications.md). Formal coverage and reproducible
verification are identified separately in [Verification.md](Verification.md).
