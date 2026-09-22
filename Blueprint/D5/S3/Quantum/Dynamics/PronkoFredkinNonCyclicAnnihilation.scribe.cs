using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class PronkoFredkinNonCyclicAnnihilationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/pronko2025fredkin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The periodic Fredkin Hamiltonian and Pronko's nonlocal operators are represented on the spin-word basis. The cyclic-shift absorption identity then forces both nonlocal operators to vanish on every non-cyclic invariant eigenstate.",
        H("Non-cyclic periodic Fredkin eigenstates are annihilated"),
        Blocks(
            DefinitionNode("sigmaPlus", "The spin-raising matrix", SigmaPlusFormula(),
                "The basis order is 0 = up and 1 = down. This is the sigma-plus matrix printed in section 2.1, p. 3."),
            DefinitionNode("sigmaMinus", "The spin-lowering matrix", SigmaMinusFormula(),
                "In the same ordered basis, this is the sigma-minus matrix printed in section 2.1, p. 3."),
            DefinitionNode("nUp", "Projection onto spin up", NUpFormula(),
                "The scalar one half is a complex scalar, I is the two-dimensional identity matrix, and qubitZ is the frozen matrix owned by D5/S3/Quantum/FiniteDimensional. The expression is the printed spin-up projector."),
            DefinitionNode("nDown", "Projection onto spin down", NDownFormula(),
                "The scalar one half is a complex scalar, I is the two-dimensional identity matrix, and qubitZ is the frozen matrix owned by D5/S3/Quantum/FiniteDimensional. The expression is the printed spin-down projector."),
            DefinitionNode("tensor", "Sitewise Kronecker product", TensorFormula(),
                "For configurations x and y, the matrix entry is the product of the corresponding one-site entries over i in Fin N. This fixes the Kronecker-product convention used below."),
            DefinitionNode("site", "A one-site operator", SiteFormula(),
                "The operator A occupies site j and every other factor is the two-dimensional identity. Site indices have type Fin N."),
            DefinitionNode("P", "Exchange of adjacent sites", PFormula(),
                "Here finRotate N j is j + 1 modulo N. The configuration permutation swaps sites j and finRotate N j, and permMatrix is its complex permutation matrix."),
            DefinitionNode("Pi", "Antisymmetric two-site projector", PiFormula(),
                "This is one half of the identity minus the adjacent-site exchange operator, as in section 2.1."),
            DefinitionNode("F", "Periodic Fredkin Hamiltonian density", FFormula(),
                "The first term projects site j onto spin up before antisymmetrizing sites j + 1 and j + 2. The second antisymmetrizes sites j and j + 1 before projecting site j + 2 onto spin down. Every addition of site indices is modulo N."),
            DefinitionNode("H", "Periodic Fredkin Hamiltonian", HFormula(),
                "The Hamiltonian is the sum of the local density over every j in Fin N, matching equation (2.3)."),
            DefinitionNode("C", "Ordered cyclic product", CFormula(),
                "The list is finRange N with its final element removed, mapped through j to P_N(j), and multiplied from left to right. Thus it is the printed ordered product P_(1,2) through P_(N-1,N), with zero-based formal site indices."),
            DefinitionNode("sigmaPow", "The three encoded local operators", SigmaPowFormula(),
                "The Fin 3 values 0, 1, and 2 encode exponents -1, 0, and 1. They select sigma-minus, the identity, and sigma-plus, respectively."),
            DefinitionNode("Sigma", "Pronko's constrained operator sum", BigSigmaFormula(),
                "The sum ranges over all r from Fin N to Fin 3 whose encoded integer exponents sum to epsilon. Each summand is the sitewise Kronecker product of sigmaPow(r_i). Hence epsilon = 1 and epsilon = -1 are exactly the two operators in equation (3.1)."),
            DefinitionNode("claim", "Pronko's Conjecture 1", ClaimDefinitionFormula(),
                "The quantifiers make the source reading explicit: N is at least three; psi is a nonzero vector in the spin-word basis; E and c are complex eigenvalues; psi is simultaneously an H-eigenvector and a C-eigenvector; and non-cyclic means c is not one."),
            TheoremNode("result", "Conjecture 1 holds", ClaimFormula(),
                "At each matrix entry (y, x), at most one Kronecker monomial has a nonzero value, determined site by site by (y_i, x_i), with total exponent equal to the number of up spins in y minus that in x. This monomial lies in the constrained sum (3.1) exactly when that difference equals epsilon; otherwise no term contributes. Every adjacent exchange preserves this weight. Consequently Sigma_epsilon P_N(j) = Sigma_epsilon, and folding through the printed ordered product gives Sigma_epsilon C_N = Sigma_epsilon. If C_N psi = c psi, then Sigma_epsilon psi = c Sigma_epsilon psi; c different from one forces the vector to vanish. The argument applies to every C-eigenvector with eigenvalue different from one. The proof uses no property of H; the hypothesis H psi = E psi is retained exactly as in Conjecture 1.",
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("pronko-2025-fredkin-noncyclic-annihilation"),
                    ResolutionKind.Proved))),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Quantum/FiniteDimensional"))]));

    private static DocumentBlock DefinitionNode(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("pronko-fredkin-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static DocumentBlock TheoremNode(string name, string title, Formula formula, string prose,
        OpenProblemResolutionClaim resolution) =>
        Describe.Lean(DescribeId.Create("pronko-fredkin-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem,
            resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula ComplexNumbers() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Named(string name)
    {
        var tokens = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (tokens.Count > 0) tokens.Add(Dot);
            tokens.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. tokens])));
    }
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula AtLeast(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Half() => new Formula.Fraction(D(1), D(2));
    private static Formula Negative(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula FinTwo() => Fin(D(2));
    private static Formula Config(Formula n) => new Formula.TypeArrow(Fin(n), FinTwo());
    private static Formula Vector(Formula n) => new Formula.TypeArrow(Config(n), ComplexNumbers());
    private static Formula MatrixTwo() => Call("Matrix", FinTwo(), FinTwo(), ComplexNumbers());
    private static Formula Identity() => F.Id("I");
    private static Formula Epsilon() => F.Id("epsilon");
    private static Formula PsiValue() => F.Id("psi");
    private static Formula BMatrix(Formula a, Formula b, Formula c, Formula d) => Seq(
        Begin, Grp(F.Id("bmatrix")), a, Amp, b, RowBreak, c, Amp, d,
        End, Grp(F.Id("bmatrix")));
    private static Formula MatrixEntry(Formula matrix, Formula y, Formula x) =>
        new Formula.Apply(matrix, [y, x]);
    private static Formula MulVec(Formula matrix, Formula vector) => Call("mulVec", matrix, vector);

    private static Formula SigmaPlusFormula() => Disp(Equal(F.Id("sigmaPlus"),
        BMatrix(D(0), D(1), D(0), D(0))));

    private static Formula SigmaMinusFormula() => Disp(Equal(F.Id("sigmaMinus"),
        BMatrix(D(0), D(0), D(1), D(0))));

    private static Formula NUpFormula() => Disp(Equal(F.Id("nUp"),
        Multiply(Half(), Add(Identity(), F.Id("qubitZ")))));

    private static Formula NDownFormula() => Disp(Equal(F.Id("nDown"),
        Multiply(Half(), Subtract(Identity(), F.Id("qubitZ")))));

    private static Formula TensorFormula()
    {
        Formula n = F.Id("N"), f = F.Id("f"), y = F.Id("y"), x = F.Id("x"), i = F.Id("i");
        Formula factor = MatrixEntry(new Formula.Apply(f, [i]),
            new Formula.Apply(y, [i]), new Formula.Apply(x, [i]));
        Formula product = Seq(new Formula.Subscript(Prod, Seq(i, Sp, InMacro, Sp, Fin(n))),
            Sp, Parenthesized(factor));
        Formula equality = Equal(MatrixEntry(Call("tensor", n, f), y, x), product);
        return Disp(All("N", Naturals(), All("f", new Formula.TypeArrow(Fin(n), MatrixTwo()),
            All("y", Config(n), All("x", Config(n), equality)))));
    }

    private static Formula SiteFormula()
    {
        Formula n = F.Id("N"), j = F.Id("j"), a = F.Id("A"), i = F.Id("i");
        Formula condition = Equal(i, j);
        Formula local = Call("ite", condition, a, Identity());
        Formula body = Equal(Call("site", n, j, a), Call("tensor", n,
            Parenthesized(Seq(i, Sp, Mapsto, Sp, local))));
        return Disp(All("N", Naturals(), All("j", Fin(n), All("A", MatrixTwo(), body))));
    }

    private static Formula PFormula()
    {
        Formula n = F.Id("N"), j = F.Id("j");
        Formula swap = Call("swap", j, Call("finRotate", n, j));
        Formula configurationSwap = Call("arrowCongr", swap, Call("Equiv.refl", FinTwo()));
        Formula body = Equal(Call("P", n, j), Call("permMatrix", ComplexNumbers(), configurationSwap));
        return Disp(All("N", Naturals(), All("j", Fin(n), body)));
    }

    private static Formula PiFormula()
    {
        Formula n = F.Id("N"), j = F.Id("j");
        Formula body = Equal(Call("Pi", n, j),
            Multiply(Half(), Subtract(Identity(), Call("P", n, j))));
        return Disp(All("N", Naturals(), All("j", Fin(n), body)));
    }

    private static Formula FFormula()
    {
        Formula n = F.Id("N"), j = F.Id("j"), jOne = Call("finRotate", n, j);
        Formula jTwo = Call("finRotate", n, jOne);
        Formula first = Multiply(Call("site", n, j, F.Id("nUp")), Call("Pi", n, jOne));
        Formula second = Multiply(Call("Pi", n, j), Call("site", n, jTwo, F.Id("nDown")));
        Formula body = Equal(Call("F", n, j), Add(first, second));
        return Disp(All("N", Naturals(), All("j", Fin(n), body)));
    }

    private static Formula HFormula()
    {
        Formula n = F.Id("N"), j = F.Id("j");
        Formula sum = Seq(new Formula.Subscript(Sum, Seq(j, Sp, InMacro, Sp, Fin(n))),
            Sp, Parenthesized(Call("F", n, j)));
        return Disp(All("N", Naturals(), Equal(Call("H", n), sum)));
    }

    private static Formula CFormula()
    {
        Formula n = F.Id("N");
        Formula indices = Call("List.dropLast", Call("List.finRange", n));
        Formula matrices = Call("List.map", Parenthesized(Seq(F.Id("j"), Sp, Mapsto, Sp,
            Call("P", n, F.Id("j")))), indices);
        Formula body = Equal(Call("C", n), Call("List.prod", matrices));
        return Disp(All("N", Naturals(), body));
    }

    private static Formula SigmaPowFormula() => Disp(new Formula.Aligned([
        Equal(Call("sigmaPow", D(0)), F.Id("sigmaMinus")),
        Equal(Call("sigmaPow", D(1)), Identity()),
        Equal(Call("sigmaPow", D(2)), F.Id("sigmaPlus"))
    ]));

    private static Formula BigSigmaFormula()
    {
        Formula n = F.Id("N"), epsilon = Epsilon(), r = F.Id("r"), i = F.Id("i");
        Formula exponent = Subtract(Call("int", Call("val", new Formula.Apply(r, [i]))), D(1));
        Formula constraint = Equal(
            Seq(new Formula.Subscript(Sum, Seq(i, Sp, InMacro, Sp, Fin(n))),
                Sp, Parenthesized(exponent)), epsilon);
        Formula indexDomain = new Formula.TypeArrow(Fin(n), Fin(D(3)));
        Formula sumIndex = Seq(r, Colon, Sp, indexDomain, Comma, Sp, constraint);
        Formula summand = Call("tensor", n, Parenthesized(Seq(i, Sp, Mapsto, Sp,
            Call("sigmaPow", new Formula.Apply(r, [i])))));
        Formula sum = Seq(new Formula.Subscript(Sum, sumIndex), Sp, Parenthesized(summand));
        Formula equality = Equal(Call("Sigma", n, epsilon), sum);
        return Disp(All("N", Naturals(), All("epsilon", Integers(), equality)));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("N"), psi = PsiValue(), energy = F.Id("E"), c = F.Id("c");
        Formula hEigen = Equal(MulVec(Call("H", n), psi), Multiply(energy, psi));
        Formula cEigen = Equal(MulVec(Call("C", n), psi), Multiply(c, psi));
        Formula nonCyclic = NotEqual(c, D(1));
        Formula plusZero = Equal(MulVec(Call("Sigma", n, D(1)), psi), D(0));
        Formula minusZero = Equal(MulVec(Call("Sigma", n, Negative(D(1))), psi), D(0));
        Formula conclusion = And(plusZero, minusZero);
        Formula implications = Implies(hEigen, Implies(cEigen, Implies(nonCyclic, conclusion)));
        Formula values = All("E", ComplexNumbers(), All("c", ComplexNumbers(), implications));
        Formula vectors = All("psi", Vector(n), Implies(NotEqual(psi, D(0)), values));
        return All("N", Naturals(), Implies(AtLeast(n, D(3)), vectors));
    }

    private static Formula ClaimDefinitionFormula() => Disp(
        new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())));

    private static Formula ClaimFormula() => Disp(ClaimBody());
}
