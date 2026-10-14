# Sharp continued-fraction bounds from exact digit runs

Let $\alpha=[a_0;a_1,a_2,\ldots]$ be irrational, let $p_i/q_i$ be its
ordinary simple continued-fraction convergents, and write
$\Theta_i=q_i|q_i\alpha-p_i|$. Fix $n\ge0$ and the central digit
$a_{n+2}=a\ge2$. Throughout this account and the Lean statements, the
chronological triple is $(\Theta_n,\Theta_{n+1},\Theta_{n+2})$.
Its finite past and infinite future coordinates are

```math
x=[0;a_{n+1},\ldots,a_1]=q_n/q_{n+1},\qquad
y=[0;a_{n+3},a_{n+4},\ldots].
```

Thus $x\in\mathbb Q\cap(0,1]$ and
$y\in(0,1)\setminus\mathbb Q$; the endpoint $x=1$ is allowed. Set

```math
T_a(t)=\frac1{a+t},\quad
\beta_a=\frac{\sqrt{a^2+4}-a}{2},\quad
c_a=\frac1{\sqrt{a^2+4}},
```

and define the two envelopes

```math
F_a(x,y)=\frac{\min\{1,x(a+y),y(a+x)\}}{a+x+y},\qquad
G_a(x,y)=\frac{\max\{1,x(a+y),y(a+x)\}}{a+x+y}.
```

The classical metallic thresholds and natural-extension geometry are
prior work. The results presented here concern exact run refinements,
rectangle optimization, and sharp inverse stability with quantitative
applications. [Sources.md](Sources.md) records the literature and access
limitations. Worldwide priority is not asserted.

## Ordinary convergents and the coordinate bridge

The ordinary continuant recurrences and determinant identity give

```math
p_{i+1}=a_{i+1}p_i+p_{i-1},\quad
q_{i+1}=a_{i+1}q_i+q_{i-1},\quad
p_iq_{i-1}-p_{i-1}q_i=(-1)^{i-1},
```

with $p_{-1}=1,q_{-1}=0,p_0=a_0,q_0=1$. The complete quotient at
position $n+2$ is $a+y$, so

```math
\alpha=\frac{p_{n+1}(a+y)+p_n}{q_{n+1}(a+y)+q_n}.
```

Subtract the three consecutive convergents and use the determinant
identity. Their actual approximation coefficients satisfy

```math
(\Theta_n,\Theta_{n+1},\Theta_{n+2})
=\frac{(x(a+y),1,y(a+x))}{a+x+y}.                         \tag{1}
```

Their minimum and maximum are therefore $F_a(x,y)$ and $G_a(x,y)$.
In Lean, the numerators and denominators come from Mathlib's continued
fraction of the real input; the digits come from the floor/fraction
algorithm. Equation (1) is proved from these definitions.

## Exact optimization on every closed rectangle

Here $a\ge1$ may be real. Let
$R=[\ell_x,u_x]\times[\ell_y,u_y]\subseteq[0,1]^2$, with either interval
possibly a singleton. Put

```math
Q(x,y)=\min\{x(a+y),y(a+x)\},\qquad
P(x,y)=\max\{x(a+y),y(a+x)\}.
```

Write $\operatorname{clip}(z;L,U)=\min\{U,\max\{L,z\}\}$. Define

```math
h(t)=\max\{1/t-a,1/(a+t)\}\quad(t>0),
```

and, on nonnegative arguments,

```math
k(t)=\begin{cases}
1/(a+t),&0\le t\le\beta_a,\\
\max\{0,1/t-a\},&t>\beta_a.
\end{cases}
```

Equivalently, $k(0)=1/a$ and
$k(t)=\max\{0,\min\{1/t-a,1/(a+t)\}\}$ for $t>0$.

The maximum $C(R)=\max_R F_a$ and all its maximizers are as follows.

1. If $u_xu_y=0$, then $F_a=0$ throughout $R$ and every point maximizes.
2. Otherwise, if $Q(u_x,u_y)\le1$, the unique maximizer is $(u_x,u_y)$
   and $C(R)=Q(u_x,u_y)/(a+u_x+u_y)$.
3. Otherwise, if $Q(\ell_x,\ell_y)\ge1$, the unique maximizer is
   $(\ell_x,\ell_y)$ and $C(R)=1/(a+\ell_x+\ell_y)$.
4. Otherwise set $L=\max\{\ell_x,h(u_y)\}$ and
   $U=\min\{u_x,h(\ell_y)\}$. When $\ell_y=0$, use $U=u_x$.
   Then $0<L\le U\le1$. The unique maximizer is
   $(x_*,y_*)=(\operatorname{clip}(\beta_a;L,U),h(x_*))$, and
   $C(R)=1/(a+x_*+y_*)$.

The minimum $U(R)=\min_R G_a$ is always unique.

1. If $P(u_x,u_y)\le1$, its minimizer is $(u_x,u_y)$ and
   $U(R)=1/(a+u_x+u_y)$.
2. Otherwise, if $P(\ell_x,\ell_y)\ge1$, its minimizer is
   $(\ell_x,\ell_y)$ and
   $U(R)=P(\ell_x,\ell_y)/(a+\ell_x+\ell_y)$.
3. Otherwise set $L=\max\{\ell_x,k(u_y)\}$ and
   $U=\min\{u_x,k(\ell_y)\}$. Then $0\le L\le U\le1/a$.
   The minimizer is
   $(x_*,y_*)=(\operatorname{clip}(\beta_a;L,U),k(x_*))$, and
   $U(R)=1/(a+x_*+y_*)$.

These formulas include line segments, singletons, and rectangles meeting
an axis. The lower formula never needs to assign a finite value to $h(0)$.

An algebraic proof starts with the four universal bounds

```math
F_a(t,u)\le\frac{t}{1+t^2},\quad
F_a(t,u)\le\frac{a+t}{1+(a+t)^2},\quad
G_a(t,u)\ge\frac{t}{1+t^2},\quad
G_a(t,u)\ge\frac{a+t}{1+(a+t)^2}.                       \tag{2}
```

They follow by splitting at $t(a+u)=1$ or $u(a+t)=1$ and clearing
positive denominators. Equality in each comparison, when its numerator
coordinate is positive, forces the corresponding product to equal one.
The function $t/(1+t^2)$ strictly increases on $[0,1]$ and strictly
decreases on $[1,\infty)$.

The lower switching curve $Q=1$ is $y=h(x)$, a decreasing involution
on positive reals. The upper switching curve $P=1$ is $y=k(x)$ for
$0\le x\le1/a$, also a decreasing involution on that interval.
The displayed $L,U$ are exactly their feasible first-coordinate ranges.
Clipping either selects the metallic point or an edge facing that point.
At such an edge, one of (2), together with its strict one-variable
monotonicity, bounds every point in the rectangle and forces the stated
unique equality point. In the noncrossing cases the two side fractions
increase coordinatewise and the central fraction decreases, giving the
indicated corner. This also proves the axis exception for $F_a$.

In particular,

```math
F_a(x,y)\le c_a\le G_a(x,y),
```

and either equality holds exactly at $(\beta_a,\beta_a)$. Consequently

```math
C(R)=c_a\iff(\beta_a,\beta_a)\in R\iff U(R)=c_a.
```

A rectangle excluding that point satisfies $C(R)<c_a<U(R)$.
Four corners do not suffice for arbitrary rectangles: on $[0,1]^2$,
$F_2(1/2,1/2)=1/3$ exceeds every corner value, while
$G_2(1/2,1/2)=5/12$ is below every corner value.

## Four corners for every exact run

For real $a>1$ and every natural $r$, form sorted image intervals

```math
I_r^L=T_a^r([1/a,1]),\qquad I_r^H=T_a^r([0,1/(a+1)]).
```

For integer $a\ge2$, $L$ means that the first departing digit is less
than $a$ and $H$ that it is greater. Let $R=I_r^e\times I_s^f$ and
let $V(R)$ be its four corners. Then

```math
C_{a;r,s}^{e,f}=\max_{v\in V(R)}F_a(v)=\max_R F_a,\qquad
U_{a;r,s}^{e,f}=\min_{v\in V(R)}G_a(v)=\min_R G_a.       \tag{3}
```

Each extremizer is a unique corner, and
$C_{a;r,s}^{e,f}<c_a<U_{a;r,s}^{e,f}$. The constants are rational when
$a$ is rational, in particular for every integer central digit.

To see why all run lengths are covered, put $K_r=T_a^r([0,1])$.
These intervals are nested, and

```math
K_r\setminus\operatorname{int}(K_{r+1})=I_r^L\cup I_r^H.
```

Strict monotonicity of $T_a^r$ implies that distinct run cells meet only
at common endpoints. Each run cell lies strictly on one side of
$\beta_a$, and $T_a(I_s^f)=I_{s+1}^f$. Thus a run cell and the image
of the other coordinate's cell are either ordered or have matching
endpoints. The switching curves $x=T_a(y)$ and $y=T_a(x)$ consequently
meet the rectangle only at corners or in a segment joining opposite
corners. Along a matching segment the objective is strictly monotone,
since the interval excludes $\beta_a$. The rectangle theorem gives (3)
and uniqueness without a cutoff or parity table.

For exact endpoint arithmetic, let $P_{-1}=1,P_0=0$ and
$P_{j+1}=aP_j+P_{j-1}$. Induction gives

```math
T_a^r(t)=\frac{P_{r-1}t+P_r}{P_rt+P_{r+1}}.             \tag{4}
```

Evaluate at $0,1/(a+1),1/a,1$, sort the endpoint pairs, and use (3).
For the silver digit, immediate departures give:

| Departure digits | $C$ | $U$ |
| --- | --- | --- |
| $1,1$ | $1/3$ | $5/12$ |
| $1,\ge3$, or reversed | $3/10$ | $2/5$ |
| $\ge3,\ge3$ | $7/24$ | $3/8$ |

With one adjacent silver digit on each side followed by low and high
departures, the constants are $10/29$ and $21/58$.

## Actual digits, strict bounds, and optimality

An exact past run has $r\le n$, with
$a_{n+1-i}=a$ for $0\le i<r$, followed by the positive departing digit
$a_{n+1-r}$. An exact future run has $a_{n+3+i}=a$ for $0\le i<s$,
followed by $a_{n+3+s}$. Each departing digit is on its specified strict
side of $a$. An exhausted past and an infinite constant future are
separate boundary classes.

The actual tails lie in the respective closed run cells. Every actual
triple in such a terminated class satisfies

```math
\min(\Theta_n,\Theta_{n+1},\Theta_{n+2})
 < C_{a;r,s}^{e,f}<c_a<U_{a;r,s}^{e,f}
 <\max(\Theta_n,\Theta_{n+1},\Theta_{n+2}).              \tag{5}
```

The first constant is the exact supremum and the second the exact
infimum over actual irrational inputs in that class. For every
$\epsilon>0$, admissible triples approach each constant within
$\epsilon$. The finite index may vary; this does not assert optimality
at an independently prescribed index.

Here is an explicit realization argument. Before the constant run is
prefixed, the endpoint tails can be reached or approached by the
following positive digit words. Every future word is completed with
the irrational tail $[0;\overline2]$.

| Departure and endpoint | Reversed finite-past word | Future prefix as $N\to\infty$ |
| --- | --- | --- |
| $L$, $1/a$ | $[a-1,1]$ | $[a-1,1,N+1]$ |
| $L$, $1$ | $[1]$ | $[1,N+1]$ |
| $H$, $0$ | $[a+N+1]$ | $[a+N+1]$ |
| $H$, $1/(a+1)$ | $[a+1]$ | $[a+1,N+1]$ |

Prefix the requisite copies of $a$, reverse the finite-past word into
chronological order, insert the central digit, and append the chosen
irrational future. The floor/fraction algorithm recovers the prescribed
words. Continuity of the fractional-linear maps and (1) proves convergence
to every corner and hence sharpness. In particular the low finite-past
endpoint $1/a=[0;a-1,1]$ is retained; canonicalizing the reversed word
would incorrectly remove it. All extremizing future corners are rational,
so the actual irrational futures never attain (5)'s outer constants.

## Optimal global inverse stability

For every real $a\ge2$, set

```math
\kappa_a=\frac{c_a(a+1-\beta_a)}{1+(a+1)^2}>0.
```

On the entire closed unit square,

```math
c_a-F_a(x,y)\ge\kappa_a\max\{|x-\beta_a|,|y-\beta_a|\}. \tag{6}
```

This coefficient is largest possible. Equality holds exactly at
$(\beta_a,\beta_a)$, $(1,1/(a+1))$, and $(1/(a+1),1)$.
For $a=2$, $\kappa_2=(2\sqrt2-1)/20$.

A direct algebraic proof uses (2). Write $\beta=\beta_a$, $c=c_a$,
and $f(t)=t/(1+t^2)$. Since $0<\beta<1/2$ and
$c=\beta/(1+\beta^2)$, for $0\le t\le\beta$ one has

```math
c-f(t)-c(\beta-t)
=\frac{(\beta-t)(1-\beta t-\beta-\beta t^2)}
 {(1+\beta^2)(1+t^2)}\ge0.
```

Moreover $\kappa_a<c$, so this gives a strictly stronger slope at every
$t<\beta$. For $\beta\le t\le1$, the metallic equation
$\beta(a+\beta)=1$ gives

```math
c-f(a+t)=c(t-\beta)\frac{a+t-\beta}{1+(a+t)^2}.
```

The last fraction is at least its value at $t=1$, because

```math
\frac{a+t-\beta}{1+(a+t)^2}-\frac{a+1-\beta}{1+(a+1)^2}
=\frac{(1-t)H(t)}{(1+(a+t)^2)(1+(a+1)^2)},
```

where
$H(t)=(a+1-\beta)(t-\beta)+a(a+1)-2>0$.
The comparison is strict for $t<1$. Choose the coordinate realizing
$\max\{|x-\beta|,|y-\beta|\}$ and apply the relevant bound in (2).
This proves (6). Away from the metallic point, equality forces that
coordinate to be $1$. Equality in its rational-envelope comparison then
forces the other coordinate to be $1/(a+1)$. These two boundary points
also prove coefficient optimality.

For integer $a\ge2$, actual triples satisfy (6) strictly. Their past is
rational and cannot equal $\beta_a$; the two other equality points have
rational future. The coefficient nevertheless remains optimal for actual
triples: take $[0;1,a,a+1,N,\overline2]$ with triple index $n=0$.
Its past is $1$ and its future tends to $1/(a+1)$, so the ratio of
deficit to distance tends to $\kappa_a$.

## Optimal inverse stability for the maximum

For every real $a\ge2$, define

```math
\lambda_a=\frac{a\beta_a}{a^2+4}
=\frac{c_a a}{1+(a+\beta_a)^2}>0.
```

The corresponding sharp estimate is

```math
G_a(x,y)-c_a\ge\lambda_a
\max\{|x-\beta_a|,|y-\beta_a|\},\qquad (x,y)\in[0,1]^2. \tag{7}
```

Equality holds only at $(\beta_a,\beta_a)$. The coefficient is nevertheless
largest possible: unlike the minimum estimate, its sharpness is a limiting
phenomenon near that point. For $a=2$, $\lambda_2=(\sqrt2-1)/4$.

Here is an algebraic proof. Write $\beta=\beta_a$, $c=c_a$,
$\lambda=\lambda_a$, and $f(z)=z/(1+z^2)$. For a coordinate $t\le\beta$,
$G_a(t,u)\ge f(a+t)$ for every $u\in[0,1]$, and

```math
f(a+t)-c-\lambda(\beta-t)
=\frac{c(\beta-t)^2\bigl(a(a+t)-2\bigr)}
 {(1+(a+t)^2)(1+(a+\beta)^2)}.
```

This is positive when $t<\beta$. For $\beta<t\le1$, the other envelope
bound $G_a(t,u)\ge f(t)$ gives

```math
\frac{f(t)-c}{t-\beta}
=\frac{1-\beta t}{(1+t^2)(1+\beta^2)}
\ge\frac{1-\beta}{2(1+\beta^2)}>\lambda.
```

Use the coordinate farthest from $\beta$ and symmetry to prove (7), with
strictness away from the center. On the switching curve
$(x,y)=(t,1/(a+t))$, as $t$ increases to $\beta$ from below,
$G_a(x,y)=f(a+t)$ and the maximum coordinate distance is $\beta-t$.
The displayed remainder divided by $\beta-t$ tends to zero, proving
coefficient optimality on the square. The hypothesis $a\ge2$ matters:
the same formula fails for $a=1$ at $(0,1)$.

For integer $a\ge2$, actual triples satisfy (7) strictly, since their
rational past cannot equal $\beta_a$. Optimality also transfers to actual
triples. Every rational $x\in(0,1]$ has a nonempty positive finite
continued-fraction word, proved by descent on its numerator. Reversing
that word, inserting the central digit $a$, and appending any irrational
$y\in(0,1)$ realizes the coordinates exactly. These pairs are dense in
the closed square. Continuity would extend any larger uniform actual
coefficient to the square, contradicting the preceding sharpness.
The finite index may vary in this argument.

## Exact one-coordinate profiles

For $0\le t\le1$, let $\phi_a(t)=\max_{0\le u\le1}F_a(t,u)$ and
$\psi_a(t)=\min_{0\le u\le1}G_a(t,u)$. Direct switching-curve optimization
gives the complete formulas

```math
\phi_a(t)=
\begin{cases}
 t(a+1)/(a+1+t),&0\le t\le1/(a+1),\\
 t/(1+t^2),&1/(a+1)\le t\le\beta_a,\\
 (a+t)/(1+(a+t)^2),&\beta_a\le t\le1,
\end{cases}
```

```math
\psi_a(t)=
\begin{cases}
 (a+t)/(1+(a+t)^2),&0\le t\le\beta_a,\\
 t/(1+t^2),&\beta_a\le t\le1/a,\\
 at/(a+t),&1/a\le t\le1.
\end{cases}
```

Corresponding maximizing coordinates are $1$, $1/t-a$, and $1/(a+t)$;
minimizing coordinates are $1/(a+t)$, $1/t-a$, and $0$. The formulas agree
at their shared endpoints. At $t=0$ every second coordinate maximizes
$F_a(0,u)=0$, and the stated witness $1$ remains valid. The lower profile
is strictly increasing up to $\beta_a$ and strictly decreasing after it;
the upper profile has the opposite monotonicity. These statements,
including endpoint attainment, are proved for every real $a\ge2$.

## Fixed pasts and constant-future boundaries

A prescribed nonempty positive chronological word $w$ fixes the entire
finite past $x=[0;w^{\mathrm{rev}}]$ and the triple index $|w|-1$.
Use the singleton first interval in the rectangle theorem. Over a
terminated future cell the two optimizing futures are rational. Both
actual inequalities are strict, and both constants are approached while
the whole word and its index remain fixed. This fixed-word result is
separate from the varying-index sharpness in (5).

If all $n+1$ past digits equal $a$, then $x=T_a^{n+1}(0)$.
If all future digits after the central one equal $a$, then $y=\beta_a$;
the converse holds as well. Over a terminated past cell and this infinite
constant future, both extrema occur at the endpoint nearest $\beta_a$.
The endpoint is $T_a^r(1/a)$ for type $L$, attained by
$[0;1,a-1,\overline a]$ at triple index $r+1$. For type $H$ it is
$T_a^r(1/(a+1))$, attained by $[0;a+1,\overline a]$ at index $r$.
These are genuine irrational equality examples.

For the fully constant input $\alpha=\beta_a=[0;\overline a]$,

```math
\Theta_k=c_a\bigl(1-(-1)^{k+1}\beta_a^{2k+2}\bigr),\qquad k\ge0.
```

The triple minimum and maximum are therefore

| Triple index | Minimum | Maximum |
| --- | --- | --- |
| $n=2j$ | $c_a(1-\beta_a^{4j+4})$ | $c_a(1+\beta_a^{4j+2})$ |
| $n=2j+1$ | $c_a(1-\beta_a^{4j+4})$ | $c_a(1+\beta_a^{4j+6})$ |

Both inequalities against $c_a$ are strict at finite indices, and both
sequences converge to $c_a$. An optional empty-past convention with a
coefficient $\Theta_{-1}=0$ is outside the ordinary triples used here.

[Applications.md](Applications.md) gives localization, effective
convergence, and the actual digit-window theorem.
[Verification.md](Verification.md) identifies the formal contracts and
reproducible checks.
