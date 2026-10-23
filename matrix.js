// The math and the explanations for the Matrix Explainer.
//
// Nothing in here touches the web page. `analyze` does the linear algebra
// and `explain` turns the results into student-friendly sections made of
// Markdown-style text and LaTeX formulas.
//
// Numbers are either exact fractions (the normal mode, a translation of
// matrix_math.py) or integers mod a prime p (the ℤ mod n mode). Both kinds of
// number have the same methods, so the row reduction code works for either.

(function () {
  "use strict";

  // -------------------------------------------------------------------------
  // Exact fractions
  // -------------------------------------------------------------------------

  function gcd(a, b) {
    if (a < 0n) a = -a;
    if (b < 0n) b = -b;
    while (b) [a, b] = [b, a % b];
    return a;
  }

  class Frac {
    constructor(n, d = 1n) {
      if (d === 0n) throw new Error("division by zero");
      if (d < 0n) {
        n = -n;
        d = -d;
      }
      const g = gcd(n, d);
      this.n = n / g;
      this.d = d / g;
    }
    add(o) { return new Frac(this.n * o.d + o.n * this.d, this.d * o.d); }
    sub(o) { return new Frac(this.n * o.d - o.n * this.d, this.d * o.d); }
    mul(o) { return new Frac(this.n * o.n, this.d * o.d); }
    div(o) { return new Frac(this.n * o.d, this.d * o.n); }
    neg() { return new Frac(-this.n, this.d); }
    abs() { return new Frac(this.n < 0n ? -this.n : this.n, this.d); }
    inverse() { return ONE.div(this); }
    zero() { return ZERO; }
    one() { return ONE; }
    fromInt(k) { return new Frac(BigInt(k)); }
    toNumber() { return Number(this.n) / Number(this.d); }
    isZero() { return this.n === 0n; }
    isOne() { return this.n === 1n && this.d === 1n; }
    isInteger() { return this.d === 1n; }
    isNegative() { return this.n < 0n; }
    equals(o) { return this.n === o.n && this.d === o.d; }
    toString() { return this.d === 1n ? `${this.n}` : `${this.n}/${this.d}`; }
    tex() {
      if (this.d === 1n) return `${this.n}`;
      const top = this.n < 0n ? -this.n : this.n;
      return `${this.n < 0n ? "-" : ""}\\frac{${top}}{${this.d}}`;
    }
  }

  const ZERO = new Frac(0n);
  const ONE = new Frac(1n);

  // -------------------------------------------------------------------------
  // Integers mod a prime p (always stored as 0, 1, ..., p - 1)
  // -------------------------------------------------------------------------

  class ModP {
    constructor(v, p) {
      this.p = p;
      this.v = ((v % p) + p) % p;
    }
    make(v) { return new ModP(v, this.p); }
    add(o) { return this.make(this.v + o.v); }
    sub(o) { return this.make(this.v - o.v); }
    mul(o) { return this.make(this.v * o.v); }
    div(o) { return this.mul(o.inverse()); }
    neg() { return this.make(-this.v); }
    abs() { return this; }
    // Extended Euclidean algorithm: finds x with v * x ≡ 1 (mod p).
    inverse() {
      if (this.v === 0n) throw new Error("division by zero");
      let [r0, r1, s0, s1] = [this.v, this.p, 1n, 0n];
      while (r1) {
        const q = r0 / r1;
        [r0, r1] = [r1, r0 - q * r1];
        [s0, s1] = [s1, s0 - q * s1];
      }
      return this.make(s0);
    }
    zero() { return this.make(0n); }
    one() { return this.make(1n); }
    fromInt(k) { return this.make(BigInt(k)); }
    isZero() { return this.v === 0n; }
    isOne() { return this.v === 1n; }
    isInteger() { return true; }
    isNegative() { return false; }
    equals(o) { return this.v === o.v; }
    toString() { return `${this.v}`; }
    tex() { return `${this.v}`; }
  }

  function fracToModP(f, p) {
    if (f.d % p === 0n) return null;
    return new ModP(f.n, p).div(new ModP(f.d, p));
  }

  // -------------------------------------------------------------------------
  // Numbers a + b√d (a, b fractions), used for eigenvalues like 1 + √2.
  // When d is negative this is a complex number: √-1 = i.
  // -------------------------------------------------------------------------

  class QSqrt {
    constructor(a, b, d) {
      this.a = a;
      this.b = b;
      this.d = d;
    }
    make(a, b) { return new QSqrt(a, b, this.d); }
    add(o) { return this.make(this.a.add(o.a), this.b.add(o.b)); }
    sub(o) { return this.make(this.a.sub(o.a), this.b.sub(o.b)); }
    mul(o) {
      const d = new Frac(this.d);
      return this.make(this.a.mul(o.a).add(this.b.mul(o.b).mul(d)),
                       this.a.mul(o.b).add(this.b.mul(o.a)));
    }
    // 1 / (a + b√d) = (a - b√d) / (a² - d·b²)
    inverse() {
      const norm = this.a.mul(this.a).sub(this.b.mul(this.b).mul(new Frac(this.d)));
      if (norm.isZero()) throw new Error("division by zero");
      return this.make(this.a.div(norm), this.b.neg().div(norm));
    }
    div(o) { return this.mul(o.inverse()); }
    neg() { return this.make(this.a.neg(), this.b.neg()); }
    abs() { return this.isNegative() ? this.neg() : this; }
    zero() { return this.make(ZERO, ZERO); }
    one() { return this.make(ONE, ZERO); }
    fromInt(k) { return this.make(new Frac(BigInt(k)), ZERO); }
    isZero() { return this.a.isZero() && this.b.isZero(); }
    isOne() { return this.a.isOne() && this.b.isZero(); }
    isInteger() { return this.b.isZero() && this.a.isInteger(); }
    isNegative() { return this.a.isZero() ? this.b.isNegative() : this.a.isNegative(); }
    equals(o) { return this.a.equals(o.a) && this.b.equals(o.b); }
    toString() { return `${this.a} + ${this.b}*sqrt(${this.d})`; }
    // As an ordinary complex number [real, imaginary] (only for checking).
    toComplex() {
      const root = Math.sqrt(Math.abs(Number(this.d)));
      const a = this.a.toNumber();
      const b = this.b.toNumber();
      return this.d < 0n ? [a, b * root] : [a + b * root, 0];
    }
    rootTex() {
      if (this.d === -1n) return "i";
      if (this.d < 0n) return `\\sqrt{${-this.d}}\\,i`;
      return `\\sqrt{${this.d}}`;
    }
    // With pm = true, writes a ± b√d (for showing a conjugate pair at once).
    tex(pm = false) {
      const { a, b } = this;
      if (b.isZero()) return a.tex();
      const root = this.rootTex();
      const size = b.abs();
      const sign = pm ? "\\pm" : b.isNegative() ? "-" : "+";
      const top = (size.n === 1n ? "" : `${size.n}`) + root;
      // (1 + √5)/2 reads better than 1/2 + √5/2
      if (!a.isZero() && a.d === size.d && a.d > 1n) {
        return `\\frac{${a.n} ${sign} ${top}}{${a.d}}`;
      }
      const bPart = size.d === 1n ? top : `\\frac{${top}}{${size.d}}`;
      if (a.isZero()) return pm ? `\\pm ${bPart}` : `${b.isNegative() ? "-" : ""}${bPart}`;
      return `${a.tex()} ${sign} ${bPart}`;
    }
  }

  // -------------------------------------------------------------------------
  // Reading what the user typed
  // -------------------------------------------------------------------------

  const NUMBER = String.raw`[+-]?(?:\d+(?:\.\d*)?|\.\d+)`;
  const ENTRY = new RegExp(`^(${NUMBER})(?:/(${NUMBER}))?$`);

  // "-1.25" -> -125/100, exactly
  function decimalToFrac(text) {
    const negative = text.startsWith("-");
    const unsigned = text.replace(/^[+-]/, "");
    const [whole, part = ""] = unsigned.split(".");
    const n = BigInt((whole || "0") + part);
    const f = new Frac(n, 10n ** BigInt(part.length));
    return negative ? f.neg() : f;
  }

  function parseEntry(text, modulus = null) {
    const cleaned = String(text).trim().replace(/−/g, "-").replace(/ /g, "");
    if (cleaned === "") throw new Error("this box is empty");
    const match = ENTRY.exec(cleaned);
    if (!match) throw new Error("I couldn't read `" + text + "` as a number");
    const top = decimalToFrac(match[1]);
    const bottom = match[2] ? decimalToFrac(match[2]) : ONE;
    if (bottom.isZero()) throw new Error("`" + text + "` divides by zero");
    const value = top.div(bottom);
    if (modulus === null) return value;
    const reduced = fracToModP(value, modulus);
    if (!reduced) {
      throw new Error("`" + text + "` can't be used mod " + modulus +
                      ", because its denominator is a multiple of " + modulus);
    }
    return reduced;
  }

  // Returns { matrix, errors }. If anything couldn't be read, matrix is null
  // and errors lists every problem cell in plain English.
  function parseGrid(grid, modulus = null) {
    const errors = [];
    const matrix = grid.map((row, i) =>
      row.map((cell, j) => {
        try {
          return parseEntry(cell, modulus);
        } catch (problem) {
          errors.push(`Row ${i + 1}, Column ${j + 1}: ${problem.message}.`);
          return null;
        }
      })
    );
    return errors.length ? { matrix: null, errors } : { matrix, errors };
  }

  const MAX_MODULUS = 1000000000;

  function smallestFactor(n) {
    for (let q = 2; q * q <= n; q++) if (n % q === 0) return q;
    return n;
  }

  function isPrime(n) {
    return n >= 2 && smallestFactor(n) === n;
  }

  // Check the n typed for ℤ mod n. Returns { modulus } (a BigInt) or { error }.
  function parseModulus(text) {
    const cleaned = String(text).trim();
    if (!/^\d+$/.test(cleaned) || Number(cleaned) < 2) {
      return { error: "For ℤ mod n, n must be a whole number that is 2 or bigger." };
    }
    const n = Number(cleaned);
    if (n > MAX_MODULUS) {
      return { error: "For ℤ mod n, please pick an n up to 1,000,000,000." };
    }
    const q = smallestFactor(n);
    if (q !== n) {
      let below = n - 1;
      while (!isPrime(below)) below--;
      let above = n + 1;
      while (!isPrime(above)) above++;
      return {
        error:
          String.raw`$\mathbb{Z}_{${n}}$ doesn't work for row reduction, because ${n} isn't prime. ` +
          String.raw`For example, $${q} \times ${n / q} = ${n} \equiv 0 \pmod{${n}}$, so $${q}$ has no ` +
          `inverse mod ${n}, and a pivot of $${q}$ could never be turned into a $1$. ` +
          `Kernels, images, and Rank–Nullity all work perfectly when n is **prime**. ` +
          `Try a prime like ${below} or ${above}.`,
      };
    }
    return { modulus: BigInt(n) };
  }

  // -------------------------------------------------------------------------
  // The linear algebra
  // -------------------------------------------------------------------------

  // Gauss–Jordan elimination. Also records every row operation as a step:
  //   { kind: "swap", col, a, b, matrix }
  //   { kind: "scale", col, row, pivot, factor, matrix }
  //   { kind: "add", col, target, source, factor, matrix }  (target -= factor × source)
  //   { kind: "skip", col, row }                           (column gets no pivot)
  function rref(A) {
    const m = A.length;
    const n = A[0].length;
    const R = A.map((row) => row.slice());
    const pivots = [];
    const steps = [];
    const snapshot = () => R.map((row) => row.slice());
    let row = 0;
    for (let col = 0; col < n && row < m; col++) {
      let p = row;
      while (p < m && R[p][col].isZero()) p++;
      if (p === m) {
        steps.push({ kind: "skip", col, row });
        continue;
      }
      if (p !== row) {
        [R[row], R[p]] = [R[p], R[row]];
        steps.push({ kind: "swap", col, a: row, b: p, matrix: snapshot() });
      }
      const pivot = R[row][col];
      if (!pivot.isOne()) {
        const factor = pivot.inverse();
        R[row] = R[row].map((x) => x.mul(factor));
        steps.push({ kind: "scale", col, row, pivot, factor, matrix: snapshot() });
      }
      for (let i = 0; i < m; i++) {
        if (i === row || R[i][col].isZero()) continue;
        const factor = R[i][col];
        R[i] = R[i].map((x, j) => x.sub(factor.mul(R[row][j])));
        steps.push({ kind: "add", col, target: i, source: row, factor, matrix: snapshot() });
      }
      pivots.push(col);
      row++;
    }
    return { R, pivots, steps };
  }

  function determinant(A) {
    const n = A.length;
    const M = A.map((row) => row.slice());
    let det = A[0][0].one();
    for (let col = 0; col < n; col++) {
      let p = col;
      while (p < n && M[p][col].isZero()) p++;
      if (p === n) return det.zero();
      if (p !== col) {
        [M[col], M[p]] = [M[p], M[col]];
        det = det.neg();
      }
      det = det.mul(M[col][col]);
      for (let i = col + 1; i < n; i++) {
        const factor = M[i][col].div(M[col][col]);
        M[i] = M[i].map((x, j) => x.sub(factor.mul(M[col][j])));
      }
    }
    return det;
  }

  // Row reduce [A | I]; the right half becomes the inverse.
  function inverse(A) {
    const n = A.length;
    const zero = A[0][0].zero();
    const one = A[0][0].one();
    const augmented = A.map((row, i) =>
      row.concat(Array.from({ length: n }, (_, j) => (i === j ? one : zero)))
    );
    return rref(augmented).R.map((row) => row.slice(n));
  }

  function column(A, j) {
    return A.map((row) => row[j]);
  }

  // Solve M x = 0 by row reducing. Returns the RREF, its pivots and free
  // columns, each x_j written in terms of the free variables, and a basis
  // for the solutions (the kernel of M).
  function solveHomogeneous(M) {
    const n = M[0].length;
    const zero = M[0][0].zero();
    const one = M[0][0].one();
    const { R, pivots, steps } = rref(M);
    const free = [];
    for (let j = 0; j < n; j++) if (!pivots.includes(j)) free.push(j);

    // Each x_j is a combination of the free variables: a Map from free
    // column -> coefficient.
    const general = Array.from({ length: n }, (_, j) => new Map([[j, one]]));
    pivots.forEach((p, row) => {
      const coefficients = new Map();
      for (const f of free) {
        if (!R[row][f].isZero()) coefficients.set(f, R[row][f].neg());
      }
      general[p] = coefficients;
    });

    // One basis vector per free variable: its coefficients.
    const basis = free.map((f) => general.map((c) => c.get(f) || zero));
    return { R, pivots, steps, free, general, basis };
  }

  // `modulus` is null for the normal mode, or the prime p for ℤ mod p.
  function analyze(A, modulus = null) {
    const m = A.length;
    const n = A[0].length;
    const { R, pivots, steps, free, general, basis: kernelBasis } = solveHomogeneous(A);
    const imageBasis = pivots.map((p) => column(A, p));

    const rank = pivots.length;
    const nullity = free.length;
    const injective = nullity === 0;
    const surjective = rank === m;
    const invertible = injective && surjective;

    return {
      A, m, n, modulus, rref: R, pivots, steps, free, general, kernelBasis, imageBasis,
      rank, nullity, injective, surjective, invertible,
      det: m === n ? determinant(A) : null,
      inverse: invertible ? inverse(A) : null,
      eigen: m === n ? eigenAnalysis(A, modulus) : null,
    };
  }

  // -------------------------------------------------------------------------
  // Polynomials (for eigenvalues)
  // -------------------------------------------------------------------------
  // A polynomial is an array of coefficients, constant term first:
  // [c0, c1, c2] means c0 + c1·λ + c2·λ².

  function trimPoly(p) {
    let k = p.length;
    while (k > 1 && p[k - 1].isZero()) k--;
    return p.slice(0, k);
  }

  const isZeroPoly = (p) => p.every((c) => c.isZero());
  const degree = (p) => trimPoly(p).length - 1;

  function polyAdd(p, q) {
    const zero = p[0].zero();
    const length = Math.max(p.length, q.length);
    return trimPoly(Array.from({ length }, (_, k) => (p[k] || zero).add(q[k] || zero)));
  }

  function polySub(p, q) {
    return polyAdd(p, q.map((c) => c.neg()));
  }

  function polyMul(p, q) {
    const out = Array.from({ length: p.length + q.length - 1 }, () => p[0].zero());
    p.forEach((a, i) => q.forEach((b, j) => { out[i + j] = out[i + j].add(a.mul(b)); }));
    return trimPoly(out);
  }

  // Long division: p = quotient × q + remainder.
  function polyDivmod(p, q) {
    q = trimPoly(q);
    const r = trimPoly(p).slice();
    const zero = p[0].zero();
    const dq = q.length - 1;
    if (r.length - 1 < dq) return { quotient: [zero], remainder: r };
    const quotient = Array.from({ length: r.length - dq }, () => zero);
    for (let k = r.length - 1; k >= dq; k--) {
      const c = r[k].div(q[dq]);
      quotient[k - dq] = c;
      for (let j = 0; j <= dq; j++) r[k - dq + j] = r[k - dq + j].sub(c.mul(q[j]));
    }
    return {
      quotient: trimPoly(quotient),
      remainder: dq === 0 ? [zero] : trimPoly(r.slice(0, dq)),
    };
  }

  const divides = (p, q) => isZeroPoly(polyDivmod(p, q).remainder);

  function monic(p) {
    p = trimPoly(p);
    const lead = p[p.length - 1];
    return p.map((c) => c.div(lead));
  }

  function polyEval(p, x) {
    let value = x.zero();
    for (let k = p.length - 1; k >= 0; k--) value = value.mul(x).add(p[k]);
    return value;
  }

  function polyDerivative(p) {
    if (p.length === 1) return [p[0].zero()];
    return p.slice(1).map((c, k) => c.mul(c.fromInt(k + 1)));
  }

  function polyGcd(p, q) {
    while (!isZeroPoly(q)) [p, q] = [q, polyDivmod(p, q).remainder];
    return monic(p);
  }

  // The same roots as p, but each one only once.
  function squarefree(p) {
    return monic(polyDivmod(p, polyGcd(p, polyDerivative(p))).quotient);
  }

  // Divide q out of p as many times as it goes: [what's left, how many times].
  function divideOut(p, q) {
    let times = 0;
    while (degree(p) >= degree(q) && divides(p, q)) {
      p = polyDivmod(p, q).quotient;
      times++;
    }
    return [p, times];
  }

  // det of a matrix whose entries are polynomials, by cofactor expansion.
  // No division is needed, so this works for fractions and for mod p.
  function polyDet(M) {
    if (M.length === 1) return trimPoly(M[0][0]);
    let total = [M[0][0][0].zero()];
    M[0].forEach((entry, j) => {
      if (isZeroPoly(entry)) return;
      const minor = M.slice(1).map((row) => row.filter((_, k) => k !== j));
      const term = polyMul(entry, polyDet(minor));
      total = j % 2 ? polySub(total, term) : polyAdd(total, term);
    });
    return total;
  }

  // The characteristic polynomial p(λ) = det(A - λI).
  function charPoly(A) {
    const minusOne = A[0][0].one().neg();
    return polyDet(A.map((row, i) => row.map((x, j) => (i === j ? [x, minusOne] : [x]))));
  }

  // -------------------------------------------------------------------------
  // Finding eigenvalues
  // -------------------------------------------------------------------------
  // Floats are only used to *guess* roots; every guess is checked exactly.

  const cx = {
    add: (x, y) => [x[0] + y[0], x[1] + y[1]],
    sub: (x, y) => [x[0] - y[0], x[1] - y[1]],
    mul: (x, y) => [x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0]],
    div: (x, y) => {
      const s = y[0] * y[0] + y[1] * y[1];
      return [(x[0] * y[0] + x[1] * y[1]) / s, (x[1] * y[0] - x[0] * y[1]) / s];
    },
    abs: (x) => Math.hypot(x[0], x[1]),
  };

  const isRealish = (z) => Math.abs(z[1]) <= 1e-7 * (1 + Math.abs(z[0]));

  // Every complex root of a fraction polynomial with no repeated roots
  // (the Durand–Kerner method), as [real, imaginary] pairs.
  function approximateRoots(p) {
    const n = p.length - 1;
    if (n < 1) return [];
    const c = p.map((x) => x.toNumber() / p[n].toNumber());
    const at = (z) => {
      let value = [0, 0];
      for (let k = n; k >= 0; k--) value = cx.add(cx.mul(value, z), [c[k], 0]);
      return value;
    };
    const radius = 1 + Math.max(...c.slice(0, n).map(Math.abs));
    let z = Array.from({ length: n }, (_, k) => {
      const angle = (2 * Math.PI * k) / n + 0.4;
      return [radius * Math.cos(angle), radius * Math.sin(angle)];
    });
    for (let round = 0; round < 2000; round++) {
      let change = 0;
      z = z.map((zk, k) => {
        let denominator = [1, 0];
        z.forEach((zj, j) => {
          if (j !== k) denominator = cx.mul(denominator, cx.sub(zk, zj));
        });
        const step = cx.div(at(zk), denominator);
        change = Math.max(change, cx.abs(step));
        return cx.sub(zk, step);
      });
      if (change <= 1e-14 * radius) break;
    }
    return z;
  }

  // The simplest fraction extremely close to x (continued fractions), or null.
  function nearbyFraction(x) {
    if (!Number.isFinite(x)) return null;
    let [h0, h1, k0, k1] = [0n, 1n, 1n, 0n];
    let y = x;
    for (let i = 0; i < 60; i++) {
      const a = Math.floor(y);
      [h0, h1] = [h1, BigInt(a) * h1 + h0];
      [k0, k1] = [k1, BigInt(a) * k1 + k0];
      const f = new Frac(h1, k1);
      if (Math.abs(f.toNumber() - x) <= 1e-8 * (1 + Math.abs(x))) return f;
      if (y === a) return null;
      y = 1 / (y - a);
    }
    return null;
  }

  // Write m = k² × d with d as small as possible.
  function splitSquare(m) {
    const sign = m < 0n ? -1n : 1n;
    let x = m < 0n ? -m : m;
    let k = 1n;
    for (let p = 2n; p * p <= x && p < 1000000n; p++) {
      while (x % (p * p) === 0n) {
        x /= p * p;
        k *= p;
      }
    }
    return { k, d: sign * x };
  }

  // Roots of λ² - sλ + q by the quadratic formula: s/2 ± (k / 2D)·√d,
  // where the discriminant s² - 4q = N/D and N·D = k²·d.
  function quadraticFactor(s, q, mult) {
    const disc = s.mul(s).sub(q.mul(new Frac(4n)));
    const { k, d } = splitSquare(disc.n * disc.d);
    const half = s.div(new Frac(2n));
    const c = new Frac(k, 2n * disc.d);
    return {
      kind: "quadratic", s, q, disc, d, mult, poly: [q, s.neg(), ONE],
      roots: [new QSqrt(half, c, d), new QSqrt(half, c.neg(), d)],
    };
  }

  // Split p(λ) (fraction coefficients) into
  //   { kind: "linear", root, mult }        fraction eigenvalues
  //   { kind: "quadratic", roots, ... }     pairs like 1 ± √2 or 2 ± 3i
  //   { kind: "other", poly, approx, ... }  roots we can only give as decimals
  function factorOverQ(f) {
    const factors = [];
    let g = f;

    // 1. Fraction roots: guess with floats, then check exactly.
    const roots = [];
    for (const z of approximateRoots(squarefree(g))) {
      if (!isRealish(z)) continue;
      const r = nearbyFraction(z[0]);
      if (r && !roots.some((s) => s.equals(r)) && polyEval(g, r).isZero()) roots.push(r);
    }
    roots.sort((x, y) => x.sub(y).toNumber());
    for (const r of roots) {
      let mult;
      [g, mult] = divideOut(g, [r.neg(), ONE]);
      factors.push({ kind: "linear", root: r, mult });
    }
    if (degree(g) < 1) return factors;

    // 2. Quadratic factors λ² - sλ + q: try pairing up the remaining roots.
    let rest = squarefree(g);
    const z = approximateRoots(rest);
    const used = new Set();
    for (let i = 0; i < z.length; i++) {
      for (let j = i + 1; j < z.length; j++) {
        if (used.has(i) || used.has(j)) continue;
        const sum = cx.add(z[i], z[j]);
        const product = cx.mul(z[i], z[j]);
        if (!isRealish(sum) || !isRealish(product)) continue;
        const s = nearbyFraction(sum[0]);
        const q = nearbyFraction(product[0]);
        if (!s || !q) continue;
        const quad = [q, s.neg(), ONE];
        if (!divides(rest, quad)) continue;
        used.add(i);
        used.add(j);
        rest = polyDivmod(rest, quad).quotient;
        let mult;
        [g, mult] = divideOut(g, quad);
        const factor = quadraticFactor(s, q, mult);
        if (factor.d !== 1n) factors.push(factor);
        // (a perfect-square discriminant means two fraction roots after all)
        else for (const r of factor.roots) factors.push({ kind: "linear", root: r.a.add(r.b), mult });
      }
    }

    // 3. Whatever is left can't be written with fractions and square roots.
    if (degree(rest) >= 1) {
      const [, mult] = divideOut(g, rest);
      factors.push({ kind: "other", poly: rest, mult, approx: z.filter((_, k) => !used.has(k)) });
    }
    return factors;
  }

  // In ℤ_p the eigenvalues are just the λ in 0..p-1 with p(λ) = 0.
  const MAX_EIGEN_SEARCH = 100000n;

  function factorModP(f, p) {
    if (p > MAX_EIGEN_SEARCH) return { factors: [], rest: null, tooBig: true };
    const factors = [];
    let g = f;
    const small = Number(p);
    for (let v = 0; v < small && degree(g) >= 1; v++) {
      // Quick check with ordinary numbers (safe, since p ≤ 100,000), then exactly.
      const coefficients = g.map((c) => Number(c.v));
      let value = 0;
      for (let k = coefficients.length - 1; k >= 0; k--) {
        value = (value * v + coefficients[k]) % small;
      }
      if (value !== 0) continue;
      const r = new ModP(BigInt(v), p);
      let mult;
      [g, mult] = divideOut(g, [r.neg(), r.one()]);
      factors.push({ kind: "linear", root: r, mult });
    }
    return { factors, rest: degree(g) >= 1 ? monic(g) : null, tooBig: false };
  }

  // Characteristic polynomial, its factors, and an eigenspace for every
  // eigenvalue we can write exactly.
  function eigenAnalysis(A, modulus) {
    const poly = charPoly(A);
    const found = modulus === null
      ? { factors: factorOverQ(poly), rest: null, tooBig: false }
      : factorModP(poly, modulus);
    const values = [];
    for (const f of found.factors) {
      if (f.kind === "linear") values.push(eigenspace(A, f.root, f.mult, false));
      if (f.kind === "quadratic") {
        const Ad = A.map((row) => row.map((x) => new QSqrt(x, ZERO, f.d)));
        for (const r of f.roots) values.push(eigenspace(Ad, r, f.mult, f.d < 0n));
      }
    }
    // Eigenvalues we can only write as decimals get decimal eigenvectors.
    const approxValues = [];
    for (const f of found.factors) {
      if (f.kind !== "other") continue;
      for (const z of f.approx) {
        const space = numericEigenspace(A, z);
        approxValues.push({ z, mult: f.mult, complex: !isRealish(z), space,
                            geo: space ? space.basis.length : null });
      }
    }
    return { poly, ...found, values, approxValues };
  }

  // Row reduce a matrix of complex floats, treating anything within tol of 0 as 0.
  function numericRref(M, tol) {
    const R = M.map((row) => row.map((z) => z.slice()));
    const m = R.length;
    const n = R[0].length;
    const pivots = [];
    let row = 0;
    for (let col = 0; col < n && row < m; col++) {
      let best = row;
      for (let i = row + 1; i < m; i++) {
        if (cx.abs(R[i][col]) > cx.abs(R[best][col])) best = i;
      }
      if (cx.abs(R[best][col]) <= tol) continue;
      [R[row], R[best]] = [R[best], R[row]];
      const pivot = R[row][col];
      R[row] = R[row].map((z) => cx.div(z, pivot));
      for (let i = 0; i < m; i++) {
        if (i === row) continue;
        const factor = R[i][col];
        R[i] = R[i].map((z, j) => cx.sub(z, cx.mul(factor, R[row][j])));
      }
      pivots.push(col);
      row++;
    }
    for (const r of R) for (let j = 0; j < n; j++) if (cx.abs(r[j]) <= tol) r[j] = [0, 0];
    return { R, pivots };
  }

  // Eigenvectors for an eigenvalue we only know as a decimal: the kernel of
  // A - zI, computed with decimals. Returns null if it can't be found reliably.
  function numericEigenspace(A, z) {
    const n = A.length;
    const M = A.map((row, i) => row.map((x, j) => {
      const entry = [x.toNumber(), 0];
      return i === j ? cx.sub(entry, z) : entry;
    }));
    const scale = Math.max(1, ...M.flat().map(cx.abs));
    // z is slightly off, so A - zI is only *nearly* singular: loosen the
    // tolerance until a free variable appears.
    for (const tol of [1e-9, 1e-7, 1e-5, 1e-3]) {
      const { R, pivots } = numericRref(M, tol * scale);
      const free = [];
      for (let j = 0; j < n; j++) if (!pivots.includes(j)) free.push(j);
      if (!free.length) continue;
      const basis = free.map((f) => {
        const v = Array.from({ length: n }, (_, j) => (j === f ? [1, 0] : [0, 0]));
        pivots.forEach((p, r) => { v[p] = cx.sub([0, 0], R[r][f]); });
        return v;
      });
      return { M, R, pivots, free, basis };
    }
    return null;
  }

  // The eigenspace for λ is the kernel of A - λI.
  function eigenspace(A, lambda, mult, complex) {
    const M = A.map((row, i) => row.map((x, j) => (i === j ? x.sub(lambda) : x)));
    const space = solveHomogeneous(M);
    return { lambda, mult, complex, M, space, geo: space.basis.length };
  }

  // -------------------------------------------------------------------------
  // Axler's method (no determinants)
  // -------------------------------------------------------------------------
  // In an n-dimensional space, v, Av, A²v, ..., Aⁿv must be dependent. The
  // first dependence gives a polynomial q with q(A)v = 0, and every root of q
  // is an eigenvalue. Repeating with e₁, e₂, ... until the vectors span the
  // whole space finds every eigenvalue.

  function matVec(A, v) {
    return A.map((row) => row.reduce((sum, x, j) => sum.add(x.mul(v[j])), v[0].zero()));
  }

  function matMul(A, B) {
    const zero = A[0][0].zero();
    return A.map((row) => B[0].map((_, j) => row.reduce((sum, x, k) => sum.add(x.mul(B[k][j])), zero)));
  }

  // Rank of a list of column vectors.
  function rankOf(vectors) {
    if (!vectors.length) return 0;
    return rref(vectors[0].map((_, i) => vectors.map((v) => v[i]))).pivots.length;
  }

  // Multiply by A until the list v, Av, A²v, ... becomes dependent.
  // Returns the vectors, the matrix K with them as columns and its RREF, and
  // q(z) = zᵏ - Σ rᵢ zⁱ where Aᵏv = Σ rᵢ Aⁱv.
  function firstDependence(A, v) {
    const vectors = [v];
    for (;;) {
      const next = matVec(A, vectors[vectors.length - 1]);
      const k = vectors.length;
      const columns = [...vectors, next];
      const K = v.map((_, i) => columns.map((c) => c[i]));
      const { R, pivots } = rref(K);
      if (!pivots.includes(k)) {
        // The earlier columns are independent, so their pivots sit in rows 0..k-1.
        const r = Array.from({ length: k }, (_, i) => R[i][k]);
        const q = [...r.map((x) => x.neg()), v[0].one()];
        return { vectors: columns, K, R, pivots, r, q };
      }
      vectors.push(next);
    }
  }

  function factorKey(f) {
    if (f.kind === "linear") return "L" + f.root;
    if (f.kind === "quadratic") return `Q${f.s},${f.q}`;
    return "O" + f.poly.map(String).join(",");
  }

  // Axler's multiplicity: the dimension of null (A - λI)ⁿ.
  function generalizedDimension(A, lambda) {
    const M = A.map((row, i) => row.map((x, j) => (i === j ? x.sub(lambda) : x)));
    let power = M;
    for (let k = 1; k < A.length; k++) power = matMul(power, M);
    return solveHomogeneous(power).basis.length;
  }

  function axlerAnalysis(A, modulus) {
    const n = A.length;
    if (modulus !== null && modulus > MAX_EIGEN_SEARCH) return { tooBig: true };
    const zero = A[0][0].zero();
    const one = A[0][0].one();
    const runs = [];
    const found = new Map(); // factor key -> factor
    const generated = []; // every independent v, Av, A²v, ... so far
    for (let j = 0; j < n && rankOf(generated) < n; j++) {
      const e = Array.from({ length: n }, (_, i) => (i === j ? one : zero));
      if (rankOf([...generated, e]) === rankOf(generated)) {
        runs.push({ j, skipped: true });
        continue;
      }
      const run = firstDependence(A, e);
      const factored = modulus === null
        ? { factors: factorOverQ(run.q), rest: null }
        : factorModP(run.q, modulus);
      const fresh = factored.factors.filter((f) => !found.has(factorKey(f)));
      for (const f of fresh) found.set(factorKey(f), f);
      generated.push(...run.vectors.slice(0, -1));
      runs.push({ j, ...run, factored: { poly: run.q, ...factored }, fresh, span: rankOf(generated) });
    }

    // Every eigenvalue we can write exactly, with Axler's multiplicity.
    const factors = [...found.values()];
    const linear = factors.filter((f) => f.kind === "linear")
      .sort((x, y) => (modulus === null ? x.root.sub(y.root).toNumber() : Number(x.root.v - y.root.v)));
    const values = linear.map((f) => ({
      lambda: f.root, complex: false, mult: generalizedDimension(A, f.root),
    }));
    for (const f of factors.filter((g) => g.kind === "quadratic")) {
      const Ad = A.map((row) => row.map((x) => new QSqrt(x, ZERO, f.d)));
      for (const r of f.roots) {
        values.push({ lambda: r, complex: f.d < 0n, mult: generalizedDimension(Ad, r) });
      }
    }
    const others = factors.filter((f) => f.kind === "other");
    const missing = runs.some((run) => run.factored && run.factored.rest);
    return { tooBig: false, runs, values, others, missing };
  }

  // -------------------------------------------------------------------------
  // LaTeX helpers
  // -------------------------------------------------------------------------

  const PIVOT_COLOR = "#e8590c";

  function variable(j) {
    return `x_{${j + 1}}`;
  }

  function cellTex(x) {
    return typeof x === "string" ? x : x.tex();
  }

  // A matrix in square brackets; entries listed in `highlight` ("i,j") are colored.
  function matrixTex(M, highlight = new Set()) {
    const rows = M.map((row, i) =>
      row
        .map((x, j) => {
          const cell = cellTex(x);
          return highlight.has(`${i},${j}`)
            ? `\\color{${PIVOT_COLOR}}{\\mathbf{${cell}}}`
            : cell;
        })
        .join(" & ")
    );
    return "\\begin{bmatrix}" + rows.join(" \\\\ ") + "\\end{bmatrix}";
  }

  function vectorTex(v) {
    return matrixTex(v.map((x) => [x]));
  }

  function setTex(vectors) {
    if (!vectors.length) return String.raw`\{\,\}`;
    return String.raw`\left\{ ` + vectors.map(vectorTex).join(", ") + String.raw` \right\}`;
  }

  function spanTex(vectors) {
    return String.raw`\operatorname{span}` + setTex(vectors);
  }

  // A combination of free variables, like "-2 x_{2} - 3 x_{4}".
  function combinationTex(coefficients, free) {
    const terms = free.filter((f) => coefficients.has(f));
    if (!terms.length) return "0";
    return terms
      .map((f, k) => {
        const c = coefficients.get(f);
        const sign = c.isNegative() ? (k === 0 ? "-" : " - ") : k === 0 ? "" : " + ";
        const size = c.abs();
        return sign + (size.isOne() ? "" : size.tex() + " ") + variable(f);
      })
      .join("");
  }

  // ℝ^k normally, ℤ_p^k in mod p mode.
  function space(a, k) {
    return a.modulus === null
      ? `\\mathbb{R}^{${k}}`
      : `\\mathbb{Z}_{${a.modulus}}^{${k}}`;
  }

  // "p^k = N", leaving off N when it would be enormous.
  function countTex(p, k) {
    const total = (p ** BigInt(k)).toString();
    return total.length > 15 ? `${p}^{${k}}` : `${p}^{${k}} = ${total}`;
  }

  // -------------------------------------------------------------------------
  // Plain-English helpers
  // -------------------------------------------------------------------------

  function plural(count, word) {
    return count === 1 ? `${count} ${word}` : `${count} ${word}s`;
  }

  function andList(items) {
    items = items.map(String);
    if (items.length <= 1) return items.join("");
    if (items.length === 2) return `${items[0]} and ${items[1]}`;
    return items.slice(0, -1).join(", ") + `, and ${items[items.length - 1]}`;
  }

  // 0-based columns -> "column 2" / "columns 1 and 3"
  function columnsPhrase(cols) {
    return `${cols.length === 1 ? "column" : "columns"} ${andList(cols.map((c) => c + 1))}`;
  }

  function rowsPhrase(rows) {
    return `${rows.length === 1 ? "row" : "rows"} ${andList(rows.map((r) => r + 1))}`;
  }

  function variablesPhrase(cols) {
    return andList(cols.map((c) => `$${variable(c)}$`));
  }

  function capitalize(text) {
    return text.charAt(0).toUpperCase() + text.slice(1);
  }

  // -------------------------------------------------------------------------
  // The explanation, section by section
  // -------------------------------------------------------------------------

  const md = (text) => ["md", text];
  const latex = (formula) => ["latex", formula];
  const raw = String.raw;

  // Returns a list of [title, blocks]. Each block is ["md", text] or ["latex", formula].
  // options.showSteps adds every row operation to the RREF section.
  function explain(a, options = {}) {
    const sections = [
      ["The Setup", setup(a)],
      ["Row Reduce to RREF", rrefSection(a, options.showSteps)],
      ["The Kernel", kernel(a)],
      ["The Image", image(a)],
      ["Is it Injective?", injectiveSection(a)],
      ["Is it Surjective?", surjectiveSection(a)],
      ["Is it Invertible?", invertibleSection(a)],
    ];
    if (a.m === a.n) sections.push(["Determinant and Inverse", squareExtras(a)]);
    sections.push(
      ["The Rank–Nullity Theorem", rankNullity(a)],
      ["Eigenvalues", options.axler ? axlerSection(a) : eigenvaluesSection(a)],
      ["Eigenvectors", eigenvectorsSection(a)]);
    return sections;
  }

  function setup(a) {
    const blocks = [
      latex("A = " + matrixTex(a.A)),
      md(raw`Our matrix $A$ has **${plural(a.m, "row")}** and **${plural(a.n, "column")}**, ` +
         raw`so it is a $${a.m} \times ${a.n}$ matrix. That means the transformation ` +
         raw`$T(\vec{x}) = A\vec{x}$ takes vectors from $${space(a, a.n)}$ (the **domain**) ` +
         raw`and sends them to $${space(a, a.m)}$ (the **codomain**).`),
    ];
    if (a.modulus !== null) {
      const p = a.modulus;
      blocks.push(md(
        raw`We're working in $\mathbb{Z}_{${p}}$, the **integers mod ${p}**. Every entry is ` +
        `replaced by its remainder when divided by ${p}, and all arithmetic wraps around ` +
        raw`at ${p}. For example, $-1 \equiv ${p - 1n}$ and $${p} \equiv 0 \pmod{${p}}$. ` +
        "Fractions work too, as long as the bottom isn't a multiple of " +
        raw`${p}: $\tfrac{1}{2}$ means the number that gives $1$ when multiplied by $2$.`));
    }
    return blocks;
  }

  function rrefSection(a, showSteps) {
    const pivotSpots = new Set(a.pivots.map((col, row) => `${row},${col}`));
    const blocks = showSteps
      ? stepBlocks(a)
      : [md("Row reducing $A$ gives its **reduced row echelon form** (RREF):")];
    blocks.push(latex(raw`\operatorname{rref}(A) = ` + matrixTex(a.rref, pivotSpots)));
    if (!a.pivots.length) {
      blocks.push(md(
        "Every entry is $0$, so there are **no pivots** at all. " +
        "That means every variable is a **free variable**."));
      return blocks;
    }
    let text = `The **pivots** (the leading 1s, shown in orange) are in ` +
               `**${columnsPhrase(a.pivots)}**.`;
    if (a.free.length) {
      text += ` The ${a.free.length === 1 ? "column" : "columns"} without a pivot ` +
              `(${columnsPhrase(a.free)}) give us **free variables**: ` +
              `${variablesPhrase(a.free)}.`;
    } else {
      text += " Every column has a pivot, so there are **no free variables**.";
    }
    blocks.push(md(text));
    return blocks;
  }

  // Every row operation, one at a time, ending just before the final RREF.
  function stepBlocks(a) {
    const mod = a.modulus !== null;
    const operations = a.steps.filter((s) => s.kind !== "skip");
    if (!operations.length) {
      return [md("$A$ is **already** in reduced row echelon form, so no row operations " +
                 "are needed:")];
    }
    const blocks = [
      md("Let's row reduce $A$ one step at a time. We work column by column: get a " +
         "nonzero number into the pivot spot, turn it into a $1$, then use it to make " +
         "every other entry in its column a $0$." +
         (mod ? ` Remember, all arithmetic is mod ${a.modulus}.` : "")),
      latex("A = " + matrixTex(a.A)),
    ];
    let count = 0;
    for (const step of a.steps) {
      if (step.kind === "skip") {
        blocks.push(md(
          `Column ${step.col + 1} has no nonzero entries at or below row ${step.row + 1}, ` +
          "so it gets **no pivot**. On to the next column."));
        continue;
      }
      count++;
      const [label, sentence] = describeStep(step, a);
      blocks.push(
        md(`**Step ${count}:** ${sentence}`),
        latex(raw`\xrightarrow{\;${label}\;}` + matrixTex(step.matrix)));
    }
    blocks.push(md("Every pivot is now a $1$ with zeros above and below it, so we've " +
                   "reached the RREF:"));
    return blocks;
  }

  // Returns [arrow label, plain-English sentence] for one row operation.
  function describeStep(step, a) {
    const R = (i) => `R_{${i + 1}}`;
    if (step.kind === "swap") {
      return [
        raw`${R(step.a)} \leftrightarrow ${R(step.b)}`,
        `Swap row ${step.a + 1} and row ${step.b + 1}, so there's a nonzero number in ` +
        `the pivot spot of column ${step.col + 1}.`,
      ];
    }
    if (step.kind === "scale") {
      const label = raw`${R(step.row)} \to ${step.factor.tex()}${R(step.row)}`;
      if (a.modulus !== null) {
        const product = step.pivot.v * step.factor.v;
        return [label,
          `Multiply row ${step.row + 1} by $${step.factor.tex()}$ to make the pivot a $1$. ` +
          raw`(In $\mathbb{Z}_{${a.modulus}}$, $${step.factor.tex()}$ is the inverse of ` +
          raw`$${step.pivot.tex()}$, because $${step.pivot.tex()} \times ${step.factor.tex()} ` +
          raw`= ${product} \equiv 1$.)`];
      }
      if (step.pivot.isInteger()) {
        return [label,
          `Divide row ${step.row + 1} by $${step.pivot.tex()}$ to make the pivot a $1$.`];
      }
      return [label,
        `Multiply row ${step.row + 1} by $${step.factor.tex()}$ to make the pivot a $1$.`];
    }
    // "add": target row minus factor times source row
    const where = step.target > step.source ? "below" : "above";
    const subtract = !step.factor.isNegative();
    const size = step.factor.abs();
    const times = size.isOne() ? "" : size.tex();
    const sentence =
      (subtract
        ? `Subtract ${size.isOne() ? "" : `$${times}$ times `}row ${step.source + 1} ` +
          `from row ${step.target + 1}`
        : `Add ${size.isOne() ? "" : `$${times}$ times `}row ${step.source + 1} ` +
          `to row ${step.target + 1}`) +
      ` to turn the $${step.factor.tex()}$ ${where} the pivot into a $0$.`;
    return [
      raw`${R(step.target)} \to ${R(step.target)} ${subtract ? "-" : "+"} ${times}${R(step.source)}`,
      sentence,
    ];
  }

  function kernel(a) {
    const blocks = [md(
      raw`The **kernel** of $A$ is the set of every vector $\vec{x}$ that $A$ sends ` +
      raw`to zero, that is, every solution of $A\vec{x} = \vec{0}$. ` +
      "We can read the solutions straight off the RREF.")];

    if (!a.free.length) {
      blocks.push(
        md("Every column of the RREF has a pivot, so there are no free variables. " +
           "Each equation pins its variable to $0$, so the **only** solution is " +
           raw`$\vec{x} = \vec{0}$.`),
        latex(raw`\ker(A) = \{\vec{0}\}`),
        md(raw`A basis for the kernel is the **empty set** $\{\,\}$, because the zero ` +
           "vector on its own can never be part of a basis. So the **nullity** of $A$ " +
           "(the dimension of the kernel) is $0$."));
      return blocks;
    }

    const one = a.free.length === 1;
    if (a.pivots.length) {
      const equations = a.pivots.map(
        (p) => `${variable(p)} &= ${combinationTex(a.general[p], a.free)}`);
      blocks.push(
        md("Each nonzero row of the RREF is an equation. Solving each one for its " +
           "pivot variable gives:" +
           (a.modulus !== null
             ? ` (Everything is mod ${a.modulus}, so a negative number like $-1$ is ` +
               `written as $${a.modulus - 1n}$.)`
             : "")),
        latex(raw`\begin{aligned}` + equations.join(raw` \\ `) + raw`\end{aligned}`),
        md(`The free ${one ? "variable" : "variables"} ${variablesPhrase(a.free)} ` +
           raw`can be **any** number. Writing $\vec{x}$ in terms of ` +
           `${one ? "it" : "them"}:`));
    } else {
      blocks.push(md("There are no equations to satisfy, so every vector works. " +
                     raw`Writing $\vec{x}$ in terms of its free variables:`));
    }

    const unknowns = Array.from({ length: a.n }, (_, j) => variable(j));
    const solved = a.general.map((c) => combinationTex(c, a.free));
    const pieces = a.free
      .map((f, k) => variable(f) + vectorTex(a.kernelBasis[k]))
      .join(" + ");
    blocks.push(
      latex(raw`\vec{x} = ` + vectorTex(unknowns) + " = " + vectorTex(solved) + " = " + pieces),
      md("So the kernel is every combination of " +
         `${a.nullity === 1 ? "this vector" : "these vectors"}:`),
      latex(raw`\ker(A) = ` + spanTex(a.kernelBasis)),
      md(a.nullity > 1
        ? `These ${plural(a.nullity, "vector")} are linearly independent ` +
          "(each one has a $1$ where the others have a $0$), so they form a " +
          "**basis for the kernel**:"
        : "This vector is not zero, so on its own it forms a **basis for the kernel**:"),
      latex(raw`\text{Basis for } \ker(A) = ` + setTex(a.kernelBasis)),
      md(`There ${a.nullity === 1 ? "is" : "are"} ${plural(a.nullity, "vector")} ` +
         `in the basis, so the **nullity** of $A$ is $${a.nullity}$.`));
    if (a.modulus !== null) {
      const p = a.modulus;
      blocks.push(md(
        `In $\\mathbb{Z}_{${p}}$, each free variable can be any of the ${p} numbers ` +
        raw`$0, 1, \dots, ${p - 1n}$, so the kernel contains exactly ` +
        `$${countTex(p, a.nullity)}$ vectors.`));
    }
    return blocks;
  }

  function image(a) {
    const blocks = [md(
      "The **image** of $A$ (also called the **column space**) is the set of every " +
      raw`output $A\vec{x}$. Since $A\vec{x}$ is always a combination of the columns ` +
      "of $A$, the image is the span of the columns of $A$.")];

    if (!a.pivots.length) {
      blocks.push(
        md("Every column of $A$ is the zero vector, so the only output is " +
           raw`$\vec{0}$:`),
        latex(raw`\operatorname{im}(A) = \{\vec{0}\}`),
        md(raw`A basis for the image is the **empty set** $\{\,\}$, so the ` +
           "**rank** of $A$ is $0$."));
      return blocks;
    }

    const which = columnsPhrase(a.pivots);
    blocks.push(
      md("We don't need every column, only the ones that aren't redundant. The pivots " +
         `tell us which ones: the pivot columns were ${which}, so we ` +
         `take ${which} **of the original matrix $A$**.`),
      md("⚠️ **Careful:** take the columns from $A$, not from the RREF! Row reducing " +
         "changes the column space, but it keeps the relationships *between* the " +
         "columns. That's why the RREF tells us **which** columns to pick, but the " +
         "vectors themselves must come from $A$."),
      latex(raw`\operatorname{im}(A) = ` + spanTex(a.imageBasis)),
      latex(raw`\text{Basis for } \operatorname{im}(A) = ` + setTex(a.imageBasis)),
      md(`There ${a.rank === 1 ? "is" : "are"} ${plural(a.rank, "vector")} in ` +
         `the basis, so the **rank** of $A$ is $${a.rank}$.`));
    if (a.modulus !== null) {
      const p = a.modulus;
      blocks.push(md(
        `Each basis vector can be multiplied by any of the ${p} numbers in ` +
        `$\\mathbb{Z}_{${p}}$, so the image contains exactly $${countTex(p, a.rank)}$ ` +
        "vectors."));
    }
    if (a.rank === a.m) {
      blocks.push(md(
        `Notice that's $${a.rank}$ independent vectors in $${space(a, a.m)}$, so the ` +
        `image is **all of** $${space(a, a.m)}$.`));
    }
    return blocks;
  }

  function injectiveSection(a) {
    const blocks = [md(
      "A transformation is **injective** (one-to-one) when different inputs always " +
      "give different outputs. For a matrix, this happens exactly when the kernel is " +
      raw`only $\{\vec{0}\}$, which means **every column of the RREF has a pivot**.`)];

    if (a.injective) {
      blocks.push(md(
        raw`✅ We found that $\ker(A) = \{\vec{0}\}$: every column has a pivot. ` +
        "So $A$ **is injective**."));
      return blocks;
    }

    blocks.push(
      md(`❌ ${capitalize(columnsPhrase(a.free))} of the RREF ` +
         `${a.free.length === 1 ? "has" : "have"} no pivot, so the kernel contains ` +
         "nonzero vectors. For example, this kernel vector:"),
      latex(raw`\vec{v} = ` + vectorTex(a.kernelBasis[0])),
      md(raw`gives $A\vec{v} = \vec{0}$, and also $A\vec{0} = \vec{0}$. Two different ` +
         "inputs land on the same output, so $A$ **is not injective**."));
    if (a.n > a.m) {
      blocks.push(md(
        `💡 **Shortcut:** $A$ has more columns ($${a.n}$) than rows ($${a.m}$). ` +
        `Each row holds at most one pivot, so there are at most $${a.m}$ pivots, ` +
        `not enough for all $${a.n}$ columns. A matrix that is wider than it is ` +
        "tall can **never** be injective."));
    }
    return blocks;
  }

  function surjectiveSection(a) {
    const blocks = [md(
      "A transformation is **surjective** (onto) when every vector in the codomain " +
      `$${space(a, a.m)}$ is an output of something. For a matrix, this happens exactly when ` +
      `the image is all of $${space(a, a.m)}$, which means **every row of the RREF has a ` +
      `pivot** (the rank equals the number of rows, $${a.m}$).`)];

    if (a.surjective) {
      blocks.push(md(
        raw`✅ $\operatorname{rank}(A) = ${a.rank}$, which equals the number of rows. ` +
        `Every row has a pivot, so the image is all of $${space(a, a.m)}$ and $A$ ` +
        "**is surjective**."));
      return blocks;
    }

    const zeroRows = [];
    for (let r = a.rank; r < a.m; r++) zeroRows.push(r);
    blocks.push(md(
      raw`❌ $\operatorname{rank}(A) = ${a.rank}$, which is less than $${a.m}$. ` +
      `${capitalize(rowsPhrase(zeroRows))} of the RREF ` +
      `${zeroRows.length === 1 ? "is" : "are"} all zeros, with no pivot. So the image ` +
      `is only a $${a.rank}$-dimensional piece of $${space(a, a.m)}$, and some vectors in ` +
      `$${space(a, a.m)}$ are never reached. $A$ **is not surjective**.`));
    if (a.n < a.m) {
      blocks.push(md(
        `💡 **Shortcut:** $A$ has fewer columns ($${a.n}$) than rows ($${a.m}$). Each ` +
        `column holds at most one pivot, so there are at most $${a.n}$ pivots, not ` +
        `enough for all $${a.m}$ rows. A matrix that is taller than it is wide can ` +
        "**never** be surjective."));
    }
    return blocks;
  }

  function invertibleSection(a) {
    if (a.invertible) {
      return [md("Since the matrix is both injective and surjective, it is invertible.")];
    }
    let reason;
    if (!a.injective && !a.surjective) {
      reason = "Since the matrix is neither injective nor surjective, it is not invertible.";
    } else if (!a.injective) {
      reason = "Since the matrix is not injective, it is not invertible.";
    } else {
      reason = "Since the matrix is not surjective, it is not invertible.";
    }
    const blocks = [md(reason)];
    if (a.m !== a.n) {
      blocks.push(md(
        "(In fact, only **square** matrices can be invertible, and $A$ is " +
        raw`$${a.m} \times ${a.n}$.)`));
    }
    return blocks;
  }

  function squareExtras(a) {
    const mod = a.modulus !== null;
    const blocks = [
      md("Because $A$ is square, we can also find its **determinant**:"),
      latex(mod
        ? raw`\det(A) \equiv ${a.det.tex()} \pmod{${a.modulus}}`
        : raw`\det(A) = ` + a.det.tex()),
    ];
    const where = mod ? raw` in $\mathbb{Z}_{${a.modulus}}$` : "";
    if (a.invertible) {
      blocks.push(
        md(raw`Since $\det(A) \neq 0$${where}, this agrees with what we found: $A$ is ` +
           "invertible. Its **inverse** is:"),
        latex("A^{-1} = " + matrixTex(a.inverse)));
    } else {
      blocks.push(md(
        raw`Since $\det(A) = 0$${where}, this agrees with what we found: $A$ is not ` +
        "invertible, so $A^{-1}$ does not exist."));
    }
    return blocks;
  }

  function rankNullity(a) {
    const r1 = a.rank === 1;
    const k1 = a.nullity === 1;
    return [
      md("The **Rank–Nullity Theorem** says that for any matrix, the rank plus the " +
         "nullity equals the **number of columns**:"),
      latex(raw`\underbrace{\operatorname{rank}(A)}_{\dim \operatorname{im}(A)} + ` +
            raw`\underbrace{\operatorname{nullity}(A)}_{\dim \ker(A)} = ` +
            raw`\underbrace{n}_{\text{columns}}`),
      md("Putting in what we found for our matrix:"),
      latex(raw`${a.rank} + ${a.nullity} = ${a.n} \quad \checkmark`),
      md(`Here's **why** it works: each of the $${a.n}$ columns of the RREF either has a ` +
         `pivot or it doesn't. The $${a.rank}$ pivot ` +
         `${r1 ? "column gives" : "columns give"} the $${a.rank}$ basis ` +
         `${r1 ? "vector" : "vectors"} for the image, and the $${a.nullity}$ ` +
         `${k1 ? "column" : "columns"} without a pivot ` +
         `${k1 ? "gives" : "give"} the $${a.nullity}$ free ` +
         `${k1 ? "variable" : "variables"}, which ` +
         `${k1 ? "gives" : "give"} the $${a.nullity}$ basis ` +
         `${k1 ? "vector" : "vectors"} for the kernel. ` +
         "**Pivot columns + free columns = all the columns.**"),
    ];
  }

  // --- Eigenvalues and eigenvectors ---

  function nonSquareEigen(a) {
    return [md(
      "Eigenvalues and eigenvectors only make sense for **square** matrices. The equation " +
      raw`$A\vec{v} = \lambda\vec{v}$ compares $A\vec{v}$, which lives in $${space(a, a.m)}$, ` +
      raw`with $\lambda\vec{v}$, which lives in $${space(a, a.n)}$. Those are only the same ` +
      "space when the number of rows equals the number of columns, and $A$ is " +
      raw`$${a.m} \times ${a.n}$.`)];
  }

  // A polynomial in λ (or another variable), highest power first,
  // like "-\lambda^{3} + 2\lambda - 1".
  function polyTex(p, v = "\\lambda") {
    const terms = [];
    for (let k = p.length - 1; k >= 0; k--) {
      const c = p[k];
      if (c.isZero()) continue;
      const size = c.abs();
      const power = k === 0 ? "" : k === 1 ? v : `${v}^{${k}}`;
      const coefficient = k > 0 && size.isOne() ? "" : size.tex();
      terms.push([c.isNegative(), coefficient + power]);
    }
    if (!terms.length) return "0";
    return terms
      .map(([negative, body], i) => (i === 0 ? (negative ? "-" : "") : negative ? " - " : " + ") + body)
      .join("");
  }

  function linearTex(root, v = "\\lambda") {
    if (root.isZero()) return v;
    return root.isNegative() ? `${v} + ${root.abs().tex()}` : `${v} - ${root.tex()}`;
  }

  // A polynomial written as a product of its factors.
  function factoredTex(e, v = "\\lambda") {
    const lead = trimPoly(e.poly)[degree(e.poly)];
    let out = lead.isOne() ? "" : lead.neg().isOne() ? "-" : lead.tex();
    const power = (m) => (m > 1 ? `^{${m}}` : "");
    const pieces = e.factors.map((f) => {
      if (f.kind === "linear") {
        return f.root.isZero() ? v + power(f.mult) : `(${linearTex(f.root, v)})${power(f.mult)}`;
      }
      return `(${polyTex(f.poly, v)})${power(f.mult)}`;
    });
    if (e.rest) pieces.push(`(${polyTex(e.rest, v)})`);
    // A lone factor like (λ² + 1) doesn't need its parentheses.
    if (out === "" && pieces.length === 1 && /^\(.*\)$/.test(pieces[0])) {
      return pieces[0].slice(1, -1);
    }
    return out + pieces.join("");
  }

  // A float eigenvalue, rounded, like "1.3247" or "-0.6624 + 0.5623i".
  function decimalTex(z) {
    const round = (x) => String(Number(x.toFixed(4)));
    if (isRealish(z) || round(Math.abs(z[1])) === "0") return round(z[0]);
    const size = round(Math.abs(z[1]));
    const imaginary = (size === "1" ? "" : size) + "i";
    if (round(z[0]) === "0") return (z[1] < 0 ? "-" : "") + imaginary;
    return `${round(z[0])} ${z[1] < 0 ? "-" : "+"} ${imaginary}`;
  }

  function eigenvaluesSection(a) {
    if (a.m !== a.n) return nonSquareEigen(a);
    const e = a.eigen;
    const p = a.modulus;
    const lambdaMatrix = a.A.map((row, i) => row.map((x, j) => {
      if (i !== j) return x.tex();
      return x.isZero() ? "-\\lambda" : `${x.tex()} - \\lambda`;
    }));
    const blocks = [
      md(raw`An **eigenvalue** of $A$ is a number $\lambda$ for which some **nonzero** vector ` +
         raw`$\vec{v}$ satisfies $A\vec{v} = \lambda\vec{v}$. In other words, $A$ doesn't change ` +
         raw`the direction of $\vec{v}$; it only stretches it by a factor of $\lambda$.`),
      md(raw`Rewriting $A\vec{v} = \lambda\vec{v}$ as $(A - \lambda I)\vec{v} = \vec{0}$, we need ` +
         raw`$A - \lambda I$ to send a nonzero vector to $\vec{0}$. That happens exactly when ` +
         raw`$A - \lambda I$ is **not invertible**, which means $\det(A - \lambda I) = 0$.`),
      latex(raw`A - \lambda I = ` + matrixTex(lambdaMatrix)),
      md(raw`Its determinant is a polynomial in $\lambda$ called the **characteristic polynomial**` +
         (p !== null ? ` (working mod ${p})` : "") + ":"),
      latex(raw`p(\lambda) = \det(A - \lambda I) = ` + polyTex(e.poly)),
    ];

    if (e.tooBig) {
      blocks.push(md(
        raw`To find its roots in $\mathbb{Z}_{${p}}$ we would have to try every number from ` +
        `$0$ to $${p - 1n}$, which is too many to check here. Pick a prime under 100,000 to ` +
        "see the eigenvalues."));
      return blocks;
    }

    const factored = factoredTex(e);
    if (factored === polyTex(e.poly)) {
      blocks.push(md(raw`The eigenvalues are the roots of $p(\lambda)$.`));
    } else {
      blocks.push(
        md(raw`The eigenvalues are the roots of $p(\lambda)$. Factoring it:`),
        latex(raw`p(\lambda) = ` + factored));
    }
    for (const f of e.factors) {
      if (f.kind === "quadratic") {
        const top = (f.s.isZero() ? "" : f.s.tex() + " ") + raw`\pm \sqrt{${f.disc.tex()}}`;
        blocks.push(
          md(`The factor $${polyTex(f.poly)}$ has no fraction roots, so we use the ` +
             "**quadratic formula**:"),
          latex(raw`\lambda = \frac{${top}}{2} = ` + f.roots[0].tex(true)));
        if (f.d < 0n) {
          blocks.push(md(
            `The number under the square root is negative ($${f.disc.tex()}$), so these two ` +
            "eigenvalues are **complex**. Complex eigenvalues of a real matrix always come in " +
            raw`**conjugate pairs** $a \pm bi$.`));
        }
      }
      if (f.kind === "other") {
        blocks.push(
          md(`The factor $${polyTex(f.poly)}$ doesn't split into pieces with fraction ` +
             "coefficients, and its roots can't be written using just fractions and square " +
             "roots. Here they are as decimals:"),
          latex(f.approx.map((z) => raw`\lambda \approx ` + decimalTex(z)).join(raw`,\quad `)));
      }
    }
    if (e.rest) {
      blocks.push(md(
        `The factor $${polyTex(e.rest)}$ has **no roots** in $\\mathbb{Z}_{${p}}$: plugging in ` +
        raw`each of $0, 1, \dots, ${p - 1n}$ never gives $0$.`));
    }

    const others = e.factors.filter((f) => f.kind === "other");
    if (!e.values.length && !others.length) {
      blocks.push(md(raw`So $A$ has **no eigenvalues** in $\mathbb{Z}_{${p}}$.`));
      return blocks;
    }
    const complexTag = raw`\text{, complex}`;
    const rows = e.values.map((v) =>
      raw`\lambda &= ${v.lambda.tex()} && \text{algebraic multiplicity } ${v.mult}` +
      (v.complex ? complexTag : ""));
    for (const f of others) {
      for (const z of f.approx) {
        rows.push(raw`\lambda &\approx ${decimalTex(z)} && \text{algebraic multiplicity } ${f.mult}` +
                  (isRealish(z) ? "" : complexTag));
      }
    }
    const total = e.factors.reduce(
      (sum, f) => sum + f.mult * (f.kind === "linear" ? 1 : degree(f.poly)), 0);
    blocks.push(
      md("So the eigenvalues are:"),
      latex(raw`\begin{aligned}` + rows.join(raw` \\ `) + raw`\end{aligned}`),
      md("The **algebraic multiplicity** of an eigenvalue is how many times it shows up as a " +
         raw`root of $p(\lambda)$. ` +
         (total === a.n
           ? `Together they add up to $${a.n}$, the size of the matrix.`
           : `Together they add up to only $${total}$, less than $${a.n}$, because part of ` +
             raw`$p(\lambda)$ has no roots in $\mathbb{Z}_{${p}}$.`)));
    return blocks;
  }

  // The Eigenvalues section using Axler's method instead of determinants.
  function axlerSection(a) {
    if (a.m !== a.n) return nonSquareEigen(a);
    const x = axlerAnalysis(a.A, a.modulus);
    const p = a.modulus;
    const whole = space(a, a.n);
    const intro = md(
      raw`An **eigenvalue** of $A$ is a number $\lambda$ for which some **nonzero** vector ` +
      raw`$\vec{v}$ satisfies $A\vec{v} = \lambda\vec{v}$. In other words, $A$ doesn't change ` +
      raw`the direction of $\vec{v}$; it only stretches it by a factor of $\lambda$.`);
    if (x.tooBig) {
      return [intro, md(
        raw`To find roots in $\mathbb{Z}_{${p}}$ we would have to try every number from $0$ to ` +
        `$${p - 1n}$, which is too many to check here. Pick a prime under 100,000 to see the ` +
        "eigenvalues.")];
    }

    const blocks = [intro, md(
      "**Axler's method** finds eigenvalues without determinants. The key fact: in " +
      `$${whole}$, any $${a.n + 1}$ vectors are linearly dependent. So if we start with a ` +
      raw`nonzero vector $\vec{v}$ and keep multiplying by $A$, the list ` +
      raw`$\vec{v}, A\vec{v}, A^{2}\vec{v}, \dots$ must become dependent by the time we reach ` +
      raw`$A^{${a.n}}\vec{v}$.`)];

    const name = (i) => (i === 0 ? raw`\vec{v}` : i === 1 ? raw`A\vec{v}` : raw`A^{${i}}\vec{v}`);
    const eigenTex = (f) => {
      if (f.kind === "linear") return [raw`\lambda = ${f.root.tex()}`];
      if (f.kind === "quadratic") return [raw`\lambda = ${f.roots[0].tex(true)}`];
      return f.approx.map((z) => raw`\lambda \approx ${decimalTex(z)}`);
    };
    let explainedWhy = false;

    x.runs.forEach((run, index) => {
      const e = raw`\vec{e}_{${run.j + 1}}`;
      if (run.skipped) {
        blocks.push(md(`We skip $${e}$: it's already in the span of the vectors we've found, ` +
                       "so it can't lead to anything new."));
        return;
      }
      const k = run.vectors.length - 1;
      const pivotSpots = new Set(run.pivots.map((col, row) => `${row},${col}`));
      const terms = run.r.map((c, i) => [c, name(i)]).filter(([c]) => !c.isZero());
      const combination = terms.length
        ? terms.map(([c, label], t) => {
            const size = c.abs();
            const sign = c.isNegative() ? (t === 0 ? "-" : " - ") : t === 0 ? "" : " + ";
            return sign + (size.isOne() ? "" : size.tex()) + label;
          }).join("")
        : raw`\vec{0}`;

      blocks.push(
        md(`**Start with $\\vec{v} = ${e}$.** Multiplying by $A$ again and again:`),
        latex(run.vectors.map((vec, i) => name(i) + " = " + vectorTex(vec)).join(raw`,\quad `)),
        md("To find the first dependence, row reduce the matrix with these vectors as columns:"),
        latex(matrixTex(run.K) + raw` \;\xrightarrow{\text{RREF}}\; ` + matrixTex(run.R, pivotSpots)),
        md(`The last column, $${name(k)}$, has no pivot, so it's a combination of the ` +
           "earlier ones:"),
        latex(name(k) + " = " + combination),
        md(raw`Moving everything to one side gives $q(A)\vec{v} = \vec{0}$, where`),
        latex("q(z) = " + polyTex(run.q, "z")));

      const factored = factoredTex(run.factored, "z");
      if (factored !== polyTex(run.q, "z")) blocks.push(latex("q(z) = " + factored));
      for (const f of run.factored.factors) {
        if (f.kind === "quadratic") {
          blocks.push(md(
            `The factor $${polyTex(f.poly, "z")}$ has no fraction roots; the quadratic formula ` +
            `gives $z = ${f.roots[0].tex(true)}$` +
            (f.d < 0n ? ", which are **complex** (a conjugate pair)." : ".")));
        }
        if (f.kind === "other") {
          blocks.push(md(
            `The factor $${polyTex(f.poly, "z")}$ has roots that can't be written with just ` +
            "fractions and square roots, so we give them as decimals."));
        }
      }
      if (run.factored.rest) {
        blocks.push(md(
          `The factor $${polyTex(run.factored.rest, "z")}$ has **no roots** in ` +
          raw`$\mathbb{Z}_{${p}}$, so it doesn't give any eigenvalues.`));
      }

      if (!explainedWhy) {
        explainedWhy = true;
        blocks.push(md(
          raw`**Why are the roots of $q$ eigenvalues?** Suppose $q(\lambda) = 0$. Then ` +
          raw`$q(z) = (z - \lambda)\,s(z)$ for a polynomial $s$ of smaller degree. Because this ` +
          raw`was the **first** dependence, $\vec{w} = s(A)\vec{v}$ is not $\vec{0}$. But ` +
          raw`$(A - \lambda I)\vec{w} = q(A)\vec{v} = \vec{0}$, so $A\vec{w} = \lambda\vec{w}$. ` +
          raw`That makes $\vec{w}$ an eigenvector and $\lambda$ an eigenvalue.`));
      }

      const fresh = run.fresh.flatMap(eigenTex).map((t) => `$${t}$`);
      // a ± pair counts as two eigenvalues
      const count = run.fresh.reduce(
        (sum, f) => sum + (f.kind === "linear" ? 1 : f.kind === "quadratic" ? 2 : f.approx.length), 0);
      blocks.push(md(fresh.length
        ? `New ${count === 1 ? "eigenvalue" : "eigenvalues"} from this vector: ` +
          `${andList(fresh)}.`
        : "This vector doesn't give any new eigenvalues."));

      const moreToDo = x.runs.slice(index + 1).some((later) => !later.skipped);
      if (moreToDo) {
        blocks.push(md(
          `So far our vectors only span a $${run.span}$-dimensional part of $${whole}$, so there ` +
          "might be eigenvalues we haven't seen yet. Let's try another starting vector."));
      }
    });

    blocks.push(md(
      `Now the vectors we've generated span all of $${whole}$, so multiplying together all the ` +
      raw`polynomials $q$ we found gives a polynomial that sends **every** vector to $\vec{0}$. ` +
      raw`If $A\vec{w} = \lambda\vec{w}$ with $\vec{w} \neq \vec{0}$, that product sends $\vec{w}$ ` +
      raw`to (the product evaluated at $\lambda$) $\cdot\,\vec{w}$, so $\lambda$ must be a root of ` +
      "one of those polynomials. **We've found every eigenvalue.**"));

    if (!x.values.length && !x.others.length) {
      blocks.push(md(raw`So $A$ has **no eigenvalues** in $\mathbb{Z}_{${p}}$.`));
      return blocks;
    }

    const complexTag = raw`\text{, complex}`;
    const rows = x.values.map((v) =>
      raw`\lambda &= ${v.lambda.tex()} && \dim \operatorname{null}(A - \lambda I)^{${a.n}} = ${v.mult}` +
      (v.complex ? complexTag : ""));
    for (const f of x.others) {
      for (const z of f.approx) {
        rows.push(raw`\lambda &\approx ${decimalTex(z)}` + (isRealish(z) ? "" : raw` && \text{complex}`));
      }
    }
    const total = x.values.reduce((sum, v) => sum + v.mult, 0);
    let ending = "";
    if (x.others.length) {
      ending = "(For the decimal eigenvalues we can't compute this exactly.)";
    } else if (total === a.n) {
      ending = `These add up to $${a.n}$, the size of the matrix.`;
    } else if (x.missing) {
      ending = `These add up to only $${total}$, less than $${a.n}$, because some of the ` +
        raw`polynomials $q$ have factors with no roots in $\mathbb{Z}_{${p}}$.`;
    }
    blocks.push(
      md("Axler defines the **multiplicity** of an eigenvalue $\\lambda$ as " +
         raw`$\dim \operatorname{null}(A - \lambda I)^{${a.n}}$ (the dimension of its ` +
         "**generalized eigenspace**). So the eigenvalues are:"),
      latex(raw`\begin{aligned}` + rows.join(raw` \\ `) + raw`\end{aligned}`));
    if (ending) blocks.push(md(ending));
    return blocks;
  }

  function eigenvectorsSection(a) {
    if (a.m !== a.n) return nonSquareEigen(a);
    const e = a.eigen;
    if (e.tooBig) {
      return [md("We need the eigenvalues first, and for this $n$ there are too many numbers to " +
                 "check. Pick a prime under 100,000.")];
    }
    const others = e.factors.filter((f) => f.kind === "other");
    if (!e.values.length && !others.length) {
      return [md(raw`$A$ has no eigenvalues in $\mathbb{Z}_{${a.modulus}}$, so it has no ` +
                 "eigenvectors there either.")];
    }

    const blocks = [md(
      raw`For each eigenvalue $\lambda$, the **eigenvectors** are the nonzero solutions of ` +
      raw`$(A - \lambda I)\vec{v} = \vec{0}$. Together with $\vec{0}$ they make up the kernel of ` +
      raw`$A - \lambda I$, called the **eigenspace** $E_\lambda$. We find it exactly like we ` +
      raw`found $\ker(A)$: row reduce, then read off the free variables.`)];
    for (const v of e.values) {
      const pivotSpots = new Set(v.space.pivots.map((col, row) => `${row},${col}`));
      const one = v.space.free.length === 1;
      blocks.push(
        md(`**For $\\lambda = ${v.lambda.tex()}$**${v.complex ? " (complex)" : ""}:`),
        latex(raw`A - \lambda I = ` + matrixTex(v.M) + raw` \;\xrightarrow{\text{RREF}}\; ` +
              matrixTex(v.space.R, pivotSpots)),
        md(`The free ${one ? "variable" : "variables"} ${variablesPhrase(v.space.free)} ` +
           `${one ? "gives" : "give"} the eigenspace:`),
        latex(`E_{${v.lambda.tex()}} = ` + spanTex(v.space.basis)),
        md(`So $\\lambda = ${v.lambda.tex()}$ has **geometric multiplicity** $${v.geo}$ (the ` +
           "number of independent eigenvectors)" +
           (v.geo === v.mult
             ? ", which matches its algebraic multiplicity."
             : `, but its algebraic multiplicity is $${v.mult}$.`)));
    }
    if (e.approxValues.length) {
      blocks.push(md(
        "The remaining eigenvalues are only known as decimals, so for them we row reduce " +
        "with decimals too. These eigenvectors are **approximate** (rounded to 4 decimal " +
        "places), but they work the same way."));
    }
    const decimals = (M) => M.map((row) => row.map(decimalTex));
    for (const v of e.approxValues) {
      const label = raw`\lambda \approx ${decimalTex(v.z)}`;
      blocks.push(md(`**For $${label}$**${v.complex ? " (complex)" : ""}:`));
      if (!v.space) {
        blocks.push(md("This one is too sensitive to rounding to find reliably with decimals."));
        continue;
      }
      const pivotSpots = new Set(v.space.pivots.map((col, row) => `${row},${col}`));
      const one = v.space.free.length === 1;
      const before = raw`A - \lambda I \approx ` + matrixTex(decimals(v.space.M));
      const after = raw`\xrightarrow{\text{RREF}}\; ` + matrixTex(decimals(v.space.R), pivotSpots);
      // complex decimals are wide, so give the RREF its own line
      blocks.push(...(v.complex ? [latex(before), latex(after)] : [latex(before + raw` \;` + after)]));
      blocks.push(
        md(`The free ${one ? "variable" : "variables"} ${variablesPhrase(v.space.free)} ` +
           `${one ? "gives" : "give"} the eigenspace:`),
        latex(raw`E_{\lambda} \approx ` + spanTex(v.space.basis.map((vec) => vec.map(decimalTex)))),
        md(`So $${label}$ has **geometric multiplicity** $${v.geo}$` +
           (v.geo === v.mult
             ? ", which matches its algebraic multiplicity."
             : `, but its algebraic multiplicity is $${v.mult}$.`)));
    }
    const verdict = diagonalizableText(a);
    if (verdict) blocks.push(md(verdict));
    return blocks;
  }

  function diagonalizableText(a) {
    const e = a.eigen;
    const where = a.modulus !== null ? raw` over $\mathbb{Z}_{${a.modulus}}$` : "";
    const short = [...e.values, ...e.approxValues].find((v) => v.geo !== null && v.geo < v.mult);
    if (short) {
      const which = short.lambda ? `= ${short.lambda.tex()}` : `\\approx ${decimalTex(short.z)}`;
      return `❌ $\\lambda ${which}$ has algebraic multiplicity $${short.mult}$ ` +
        `but only ${plural(short.geo, "independent eigenvector")}, so $A$ can't have ` +
        `$${a.n}$ independent eigenvectors in total. That means $A$ ` +
        `**is not diagonalizable**${where}.`;
    }
    if (e.rest) {
      return raw`❌ Part of $p(\lambda)$ has no roots in $\mathbb{Z}_{${a.modulus}}$, so $A$ ` +
        `doesn't have enough eigenvalues there, and it **is not diagonalizable**${where}.`;
    }
    if (e.approxValues.some((v) => v.geo === null)) return null;
    const complex = e.values.some((v) => v.complex) || e.approxValues.some((v) => v.complex);
    const verdict = "✅ Every eigenvalue has as many independent eigenvectors as its algebraic " +
      `multiplicity, so together they give $${a.n}$ independent eigenvectors. That means $A$ ` +
      `**is diagonalizable**${where}`;
    return complex
      ? verdict + ", but only if we allow **complex** numbers. Using only real numbers, it isn't."
      : verdict + ".";
  }

  // A short LaTeX list of the eigenvalues for the summary tile (square matrices only).
  function eigenSummary(a) {
    if (a.m !== a.n) return null;
    const e = a.eigen;
    if (e.tooBig) return raw`\text{too many to check}`;
    const times = (m) => (m > 1 ? raw`\,(\times ${m})` : "");
    const items = [];
    for (const f of e.factors) {
      if (f.kind === "linear") items.push(f.root.tex() + times(f.mult));
      if (f.kind === "quadratic") items.push(f.roots[0].tex(true) + times(f.mult));
      if (f.kind === "other") {
        for (const z of f.approx) items.push(raw`\approx ${decimalTex(z)}` + times(f.mult));
      }
    }
    return items.length ? items.join(raw`,\; `) : raw`\text{none in } \mathbb{Z}_{${a.modulus}}`;
  }

  const api = {
    Frac, ModP, QSqrt, parseEntry, parseGrid, parseModulus, analyze, explain, eigenSummary,
    axlerAnalysis,
  };
  if (typeof module !== "undefined" && module.exports) module.exports = api;
  else window.MatrixMath = api;
})();
