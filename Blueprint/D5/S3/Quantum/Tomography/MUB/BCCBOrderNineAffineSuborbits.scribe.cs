using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.MUB;

internal sealed class BCCBOrderNineAffineSuborbitsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Tomography/MUB/BCCBOrderNineAffineSuborbits.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/karlsson2016bccbhadamard");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonconstant affine dephasing of the order-nine BCCB sum-one locus lies in the cancelling-pair or equilateral-triple family.",
        H("Affine suborbits of the order-nine BCCB family"), Blocks(
            Paragraph(Text(
                "Use zero-based matrix indices 0 through 8 and parameter positions 0 through 3. "
                    + "Fin(n) denotes the index set from 0 to n minus one. The parameter space "
                    + "Fin(p) to R is R to the power p, and LinR denotes real linear maps. "
                    + "Write i for the imaginary unit and omega for the positive cubic root in "),
                Ref("D5/S3/Observer/WindowRegister.windowRoot"), Text(":")),
            new DocumentBlock.DisplayFormula(Disp(RootFormula())),
            Node("bccb", "The symmetric block-circulant matrix", MatrixFormula(),
                "The rows and columns of this array are ordered 0 through 8. It is the "
                    + "matrix of Section 4, Eq. (4.1). Its definition allows arbitrary complex "
                    + "x, y, u and w; unimodularity and the sum-one condition enter the classification below.",
                AssessedProvenance.FromLiterature(Source)),
            Node("dephase", "Canonical dephasing", DephaseFormula(),
                "Divide entry ab by the product of entry a0 and entry 0b. On matrices with "
                    + "nonzero first row and column and entry 00 equal to one, this makes the "
                    + "first row and column equal to one. The definition itself is total, using "
                    + "complex division also when a denominator is zero.",
                AssessedProvenance.FromLiterature(Source)),
            Node("params", "The four parameter functions", ParamsFormula(),
                "The ordered tuple retains the parameter positions x, y, u, w. Each function "
                    + "is defined on the whole real parameter space; later equalities are required only on U.",
                AssessedProvenance.FromRepo(Source)),
            Node("IsAffineOn", "Affine phases on a set", AffineFormula(),
                "For each matrix entry ab, choose its own complex coefficient c(ab) and real "
                    + "linear form L(ab). The entry is c(ab) times exp(i L(ab)(t)) throughout U. "
                    + "The coefficient includes a constant phase. This predicate alone imposes "
                    + "no openness, nonemptiness, continuity or unit-modulus assumption.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("karlsson-bccb-affine-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The affine-suborbit classification"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "This is the parameter-space formulation of Karlsson's Conjecture 3. "
                        + "The set U is any nonempty open subset of a finite-dimensional real "
                        + "space. On U the four parameters have modulus one, sum to one, and "
                        + "give an affine dephasing. Nonconstancy means that two points of U "
                        + "have different ordered parameter tuples. A single permutation, "
                        + "independent of t, then puts every tuple into one of the two displayed "
                        + "families from Sections 8.1 and 8.2. No connectedness assumption or "
                        + "positive-dimension hypothesis is added; nonconstancy excludes dimension zero. "
                        + "The functions mu and xi are defined on the whole parameter space. "
                        + "Their values on U have modulus one by the tuple identities and the hypotheses."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("karlsson-bccb-affine-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Only the cancelling pair and equilateral triple occur"),
                StatementSource.FromAuthor(Disp(Named("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Let D(t) be the dephasing of H(x(t), y(t), u(t), w(t)). Its entries "
                            + "at the zero-based positions (1,2), (3,6), (4,8) and (5,7) are "
                            + "respectively 1/x(t), 1/y(t), 1/u(t) and 1/w(t). Inverting their "
                            + "affine expressions writes each parameter as c(j) exp(i L(j)(t)), "
                            + "where every coefficient c(j) has modulus one.")),
                    Paragraph(Text(
                        "The sum of these four exponential functions is real analytic on the "
                            + "whole parameter space. Since it equals one on a nonempty open set, "
                            + "analytic continuation makes the sum identity hold everywhere. "
                            + "The functions t maps to exp(i L(j)(t)) are characters of the "
                            + "additive parameter group. Linear independence of distinct characters "
                            + "forces the coefficients in the trivial-character class to sum to "
                            + "one, and those in each nontrivial class to sum to zero.")),
                    Paragraph(Text(
                        "The trivial class is nonempty. Every nontrivial class that occurs "
                            + "contains at least two members, since its coefficients are nonzero "
                            + "and sum to zero. Nonconstancy supplies such a class. With only "
                            + "four positions, there is exactly one nontrivial class, of size "
                            + "two or three, and all remaining positions belong to the trivial class.")),
                    Paragraph(Text(
                        "If the nontrivial class has size two, its coefficients are a and "
                            + "minus a. The two constant coefficients b and c have modulus one "
                            + "and satisfy b + c = 1. Thus b squared minus b plus one equals "
                            + "zero, and the constants are minus omega and minus omega squared "
                            + "in either order. Taking mu(t) to be a times the common character "
                            + "gives the cancelling-pair family.")),
                    Paragraph(Text(
                        "If the nontrivial class has size three, the remaining constant is "
                            + "one. Its three unit coefficients a, b, c sum to zero. Dividing "
                            + "by a shows that b/a and c/a are omega and omega squared in "
                            + "either order. Taking xi(t) to be a times the common character "
                            + "gives the equilateral-triple family. In both cases a fixed "
                            + "permutation arranges the positions as in the claim."))),
                DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose,
        AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("karlsson-bccb-affine-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Member(Formula point, Formula set) =>
        new Formula.Relation(point, FormulaRelationOperator.MemberOf, set);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
    private static Formula ImpliesFormula(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Negative(Formula value) => Seq(Minus, Parenthesized(value));
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula NumberSet(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula Reals() => NumberSet("R");
    private static Formula Complexes() => NumberSet("C");
    private static Formula Index(Formula n) => Call("Fin", n);
    private static Formula Space(Formula p) => Parenthesized(new Formula.TypeArrow(Index(p), Reals()));
    private static Formula Functions(Formula p) => Parenthesized(new Formula.TypeArrow(Space(p), Complexes()));
    private static Formula Matrices() => Call("Matrix", Index(D(9)), Index(D(9)), Complexes());
    private static Formula Entry(Formula matrix, Formula a, Formula b) =>
        new Formula.Subscript(matrix, Seq(a, Comma, b));
    private static Formula Tuple(Formula a, Formula b, Formula c, Formula d) =>
        Seq(OpenBracket, a, Comma, Sp, b, Comma, Sp, c, Comma, Sp, d, CloseBracket);
    private static Formula Phase(Formula form, Formula t) => Call("exp", Mul(At(form, t), F.Id("i")));
    private static Formula ParameterTuple(Formula x, Formula y, Formula u, Formula w, Formula t) =>
        Call("params", x, y, u, w, t);

    private static Formula RootFormula() =>
        Seq(Omega, Sp, Eq, Sp, Call("windowRoot", D(3)), Sp, Eq, Sp,
            new Formula.Power(F.Id("e"), new Formula.Fraction(Mul(Mul(D(2), Pi), F.Id("i")), D(3))));

    private static Formula MatrixFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), u = F.Id("u"), w = F.Id("w");
        Formula array = Seq(Begin, Grp(F.Id("pmatrix")),
            D(1), Amp, x, Amp, x, Amp, y, Amp, u, Amp, w, Amp, y, Amp, w, Amp, u, RowBreak,
            x, Amp, D(1), Amp, x, Amp, w, Amp, y, Amp, u, Amp, u, Amp, y, Amp, w, RowBreak,
            x, Amp, x, Amp, D(1), Amp, u, Amp, w, Amp, y, Amp, w, Amp, u, Amp, y, RowBreak,
            y, Amp, w, Amp, u, Amp, D(1), Amp, x, Amp, x, Amp, y, Amp, u, Amp, w, RowBreak,
            u, Amp, y, Amp, w, Amp, x, Amp, D(1), Amp, x, Amp, w, Amp, y, Amp, u, RowBreak,
            w, Amp, u, Amp, y, Amp, x, Amp, x, Amp, D(1), Amp, u, Amp, w, Amp, y, RowBreak,
            y, Amp, u, Amp, w, Amp, y, Amp, w, Amp, u, Amp, D(1), Amp, x, Amp, x, RowBreak,
            w, Amp, y, Amp, u, Amp, u, Amp, y, Amp, w, Amp, x, Amp, D(1), Amp, x, RowBreak,
            u, Amp, w, Amp, y, Amp, w, Amp, u, Amp, y, Amp, x, Amp, x, Amp, D(1),
            End, Grp(F.Id("pmatrix")));
        return All(x, Complexes(), All(y, Complexes(), All(u, Complexes(), All(w, Complexes(),
            Equal(Call("bccb", x, y, u, w), array)))));
    }

    private static Formula DephaseFormula()
    {
        Formula h = F.Id("H"), a = F.Id("a"), b = F.Id("b");
        return All(h, Matrices(), All(a, Index(D(9)), All(b, Index(D(9)),
            Equal(Entry(Call("dephase", h), a, b), new Formula.Fraction(Entry(h, a, b),
                Parenthesized(Mul(Entry(h, a, D(0)), Entry(h, D(0), b))))))));
    }

    private static Formula ParamsFormula()
    {
        Formula p = F.Id("p"), x = F.Id("x"), y = F.Id("y"), u = F.Id("u"), w = F.Id("w"), t = F.Id("t");
        return All(p, NumberSet("N"), All(x, Functions(p), All(y, Functions(p),
            All(u, Functions(p), All(w, Functions(p), All(t, Space(p),
                Equal(ParameterTuple(x, y, u, w, t), Tuple(At(x, t), At(y, t), At(u, t), At(w, t)))))))));
    }

    private static Formula AffineFormula()
    {
        Formula p = F.Id("p"), set = F.Id("U"), f = F.Id("F"), a = F.Id("a"), b = F.Id("b"), t = F.Id("t");
        Formula c = Entry(F.Id("c"), a, b), form = Entry(F.Id("L"), a, b);
        Formula entries = All(a, Index(D(9)), All(b, Index(D(9)),
            Some(c, Complexes(), Some(form, Call("LinR", Space(p), Reals()),
                All(t, Space(p), ImpliesFormula(Member(t, set),
                    Equal(Entry(At(f, t), a, b), Mul(c, Phase(form, t)))))))));
        return All(p, NumberSet("N"), All(set, Call("Set", Space(p)),
            All(f, Parenthesized(new Formula.TypeArrow(Space(p), Matrices())),
                Logic(Call("IsAffineOn", set, f), FormulaLogicOperator.Iff, entries))));
    }

    private static Formula ClaimFormula()
    {
        Formula p = F.Id("p"), set = F.Id("U"), x = F.Id("x"), y = F.Id("y"), u = F.Id("u"), w = F.Id("w");
        Formula t = F.Id("t"), first = new Formula.Subscript(t, D(1)), second = new Formula.Subscript(t, D(2));
        Formula permutation = Pi, mu = Mu, xi = Xi;
        Formula norm(Formula function) => Equal(new Formula.Absolute(At(function, t)), D(1));
        Formula unitSum = All(t, Space(p), ImpliesFormula(Member(t, set),
            And(norm(x), And(norm(y), And(norm(u), And(norm(w),
                Equal(Add(Add(Add(At(x, t), At(y, t)), At(u, t)), At(w, t)), D(1))))))));
        Formula family = Seq(t, Sp, Mapsto, Sp,
            Call("dephase", Call("bccb", At(x, t), At(y, t), At(u, t), At(w, t))));
        Formula nonconstant = Some(first, Space(p), And(Member(first, set),
            Some(second, Space(p), And(Member(second, set),
                NotEqual(ParameterTuple(x, y, u, w, first), ParameterTuple(x, y, u, w, second))))));
        Formula permuted = Parenthesized(Seq(ParameterTuple(x, y, u, w, t), Sp, Circ, Sp, permutation));
        Formula pair = Some(mu, Functions(p), All(t, Space(p), ImpliesFormula(Member(t, set),
            Equal(permuted, Tuple(At(mu, t), Negative(At(mu, t)), Negative(Omega), Negative(Square(Omega)))))));
        Formula triple = Some(xi, Functions(p), All(t, Space(p), ImpliesFormula(Member(t, set),
            Equal(permuted, Tuple(D(1), At(xi, t), Mul(Omega, At(xi, t)), Mul(Square(Omega), At(xi, t)))))));
        Formula conclusion = Some(permutation, Call("Perm", Index(D(4))),
            Logic(pair, FormulaLogicOperator.Or, triple));
        Formula parameters = All(x, Functions(p), All(y, Functions(p), All(u, Functions(p), All(w, Functions(p),
            ImpliesFormula(unitSum, ImpliesFormula(Call("IsAffineOn", set, Parenthesized(family)),
                ImpliesFormula(nonconstant, conclusion)))))));
        Formula statement = All(p, NumberSet("N"), All(set, Call("Set", Space(p)),
            ImpliesFormula(Call("IsOpen", set), ImpliesFormula(Call("Nonempty", set), parameters))));
        return Logic(Named("claim"), FormulaLogicOperator.Iff, statement);
    }
}
