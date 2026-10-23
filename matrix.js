// The math and the explanations for the Matrix Explainer.
//
// Nothing in here touches the web page. `analyze` does the linear algebra
// with exact fractions, and `explain` turns the results into student-friendly
// sections made of Markdown-style text and LaTeX formulas.
//
// This is a translation of matrix_math.py (the Python version). Every number
// is an exact fraction, so there is never any rounding.

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
    isZero() { return this.n === 0n; }
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

  function parseEntry(text) {
    const cleaned = String(text).trim().replace(/−/g, "-").replace(/ /g, "");
    if (cleaned === "") throw new Error("this box is empty");
    const match = ENTRY.exec(cleaned);
    if (!match) throw new Error("I couldn't read `" + text + "` as a number");
    const top = decimalToFrac(match[1]);
    const bottom = match[2] ? decimalToFrac(match[2]) : ONE;
    if (bottom.isZero()) throw new Error("`" + text + "` divides by zero");
    return top.div(bottom);
  }

  // Returns { matrix, errors }. If anything couldn't be read, matrix is null
  // and errors lists every problem cell in plain English.
  function parseGrid(grid) {
    const errors = [];
    const matrix = grid.map((row, i) =>
      row.map((cell, j) => {
        try {
          return parseEntry(cell);
        } catch (problem) {
          errors.push(`Row ${i + 1}, Column ${j + 1}: ${problem.message}.`);
          return null;
        }
      })
    );
    return errors.length ? { matrix: null, errors } : { matrix, errors };
  }

  // -------------------------------------------------------------------------
  // The linear algebra
  // -------------------------------------------------------------------------

  function rref(A) {
    const m = A.length;
    const n = A[0].length;
    const R = A.map((row) => row.slice());
    const pivots = [];
    let row = 0;
    for (let col = 0; col < n && row < m; col++) {
      let p = row;
      while (p < m && R[p][col].isZero()) p++;
      if (p === m) continue;
      [R[row], R[p]] = [R[p], R[row]];
      const pivot = R[row][col];
      R[row] = R[row].map((x) => x.div(pivot));
      for (let i = 0; i < m; i++) {
        if (i === row || R[i][col].isZero()) continue;
        const factor = R[i][col];
        R[i] = R[i].map((x, j) => x.sub(factor.mul(R[row][j])));
      }
      pivots.push(col);
      row++;
    }
    return { R, pivots };
  }

  function determinant(A) {
    const n = A.length;
    const M = A.map((row) => row.slice());
    let det = ONE;
    for (let col = 0; col < n; col++) {
      let p = col;
      while (p < n && M[p][col].isZero()) p++;
      if (p === n) return ZERO;
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
    const augmented = A.map((row, i) =>
      row.concat(Array.from({ length: n }, (_, j) => (i === j ? ONE : ZERO)))
    );
    return rref(augmented).R.map((row) => row.slice(n));
  }

  function column(A, j) {
    return A.map((row) => row[j]);
  }

  function analyze(A) {
    const m = A.length;
    const n = A[0].length;
    const { R, pivots } = rref(A);
    const free = [];
    for (let j = 0; j < n; j++) if (!pivots.includes(j)) free.push(j);

    // Solve A x = 0. Each x_j is written as a combination of the free
    // variables: a Map from free column -> coefficient.
    const general = Array.from({ length: n }, (_, j) => new Map([[j, ONE]]));
    pivots.forEach((p, row) => {
      const coefficients = new Map();
      for (const f of free) {
        if (!R[row][f].isZero()) coefficients.set(f, R[row][f].neg());
      }
      general[p] = coefficients;
    });

    // One kernel basis vector per free variable: its coefficients.
    const kernelBasis = free.map((f) => general.map((c) => c.get(f) || ZERO));
    const imageBasis = pivots.map((p) => column(A, p));

    const rank = pivots.length;
    const nullity = free.length;
    const injective = nullity === 0;
    const surjective = rank === m;
    const invertible = injective && surjective;

    return {
      A, m, n, rref: R, pivots, free, general, kernelBasis, imageBasis,
      rank, nullity, injective, surjective, invertible,
      det: m === n ? determinant(A) : null,
      inverse: invertible ? inverse(A) : null,
    };
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
        return sign + (size.equals(ONE) ? "" : size.tex() + " ") + variable(f);
      })
      .join("");
  }

  function R(k) {
    return `\\mathbb{R}^{${k}}`;
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
  function explain(a) {
    const sections = [
      ["The Setup", setup(a)],
      ["Row Reduce to RREF", rrefSection(a)],
      ["The Kernel", kernel(a)],
      ["The Image", image(a)],
      ["Is it Injective?", injectiveSection(a)],
      ["Is it Surjective?", surjectiveSection(a)],
      ["Is it Invertible?", invertibleSection(a)],
    ];
    if (a.m === a.n) sections.push(["Determinant and Inverse", squareExtras(a)]);
    sections.push(["The Rank–Nullity Theorem", rankNullity(a)]);
    return sections;
  }

  function setup(a) {
    return [
      latex("A = " + matrixTex(a.A)),
      md(raw`Our matrix $A$ has **${plural(a.m, "row")}** and **${plural(a.n, "column")}**, ` +
         raw`so it is a $${a.m} \times ${a.n}$ matrix. That means the transformation ` +
         raw`$T(\vec{x}) = A\vec{x}$ takes vectors from $${R(a.n)}$ (the **domain**) ` +
         raw`and sends them to $${R(a.m)}$ (the **codomain**).`),
    ];
  }

  function rrefSection(a) {
    const pivotSpots = new Set(a.pivots.map((col, row) => `${row},${col}`));
    const blocks = [
      md("Row reducing $A$ gives its **reduced row echelon form** (RREF):"),
      latex(raw`\operatorname{rref}(A) = ` + matrixTex(a.rref, pivotSpots)),
    ];
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
           "pivot variable gives:"),
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
    if (a.rank === a.m) {
      blocks.push(md(
        `Notice that's $${a.rank}$ independent vectors in $${R(a.m)}$, so the ` +
        `image is **all of** $${R(a.m)}$.`));
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
      `$${R(a.m)}$ is an output of something. For a matrix, this happens exactly when ` +
      `the image is all of $${R(a.m)}$, which means **every row of the RREF has a ` +
      `pivot** (the rank equals the number of rows, $${a.m}$).`)];

    if (a.surjective) {
      blocks.push(md(
        raw`✅ $\operatorname{rank}(A) = ${a.rank}$, which equals the number of rows. ` +
        `Every row has a pivot, so the image is all of $${R(a.m)}$ and $A$ ` +
        "**is surjective**."));
      return blocks;
    }

    const zeroRows = [];
    for (let r = a.rank; r < a.m; r++) zeroRows.push(r);
    blocks.push(md(
      raw`❌ $\operatorname{rank}(A) = ${a.rank}$, which is less than $${a.m}$. ` +
      `${capitalize(rowsPhrase(zeroRows))} of the RREF ` +
      `${zeroRows.length === 1 ? "is" : "are"} all zeros, with no pivot. So the image ` +
      `is only a $${a.rank}$-dimensional piece of $${R(a.m)}$, and some vectors in ` +
      `$${R(a.m)}$ are never reached. $A$ **is not surjective**.`));
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
    const blocks = [
      md("Because $A$ is square, we can also find its **determinant**:"),
      latex(raw`\det(A) = ` + a.det.tex()),
    ];
    if (a.invertible) {
      blocks.push(
        md(raw`Since $\det(A) \neq 0$, this agrees with what we found: $A$ is ` +
           "invertible. Its **inverse** is:"),
        latex("A^{-1} = " + matrixTex(a.inverse)));
    } else {
      blocks.push(md(
        raw`Since $\det(A) = 0$, this agrees with what we found: $A$ is not ` +
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

  const api = { Frac, parseEntry, parseGrid, analyze, explain };
  if (typeof module !== "undefined" && module.exports) module.exports = api;
  else window.MatrixMath = api;
})();
