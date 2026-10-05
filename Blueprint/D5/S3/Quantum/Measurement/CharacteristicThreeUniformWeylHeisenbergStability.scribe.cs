using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class CharacteristicThreeUniformWeylHeisenbergStabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/zhu2026uniformly");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zhu and Wang (arXiv:2608.11850) measure the stability of a minimal Weyl-Heisenberg measurement by the smallest nonidentity eigenvalue of its projector Gram matrix, construct uniformly stable finite-field families in characteristic two and in characteristic at least five, and leave characteristic three open. For every q = 3^r the fiducial obtained by adding the basis vector at 0 to the uniform vector and normalizing has projector-Gram floor at least (1/8) q/(q + 1) on the complement of the constant vector, so eta is at least 1/8 for every r.",
        H("A uniformly stable minimal Weyl-Heisenberg measurement in characteristic three"),
        Blocks(
            Node("field", "The field", FieldFormula(),
                "F(r) is the Galois field GF(3^r), the field F_q of the paper at p = 3; for r >= 1 it has q = 3^r elements.",
                "F", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("character", "The canonical additive character", CharacterFormula(),
                "The paper's psi(x) = exp(2 pi i Tr(x)/p) at p = 3, where Tr is the trace of F(r) over ZMod 3 and val is its representative in {0, 1, 2}.",
                "psi", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("displacement", "The displacement operators", DisplacementFormula(),
                "D_{a,b} = X_a Z_b with X_a|x> = |x + a> and Z_b|x> = psi(b x)|x>: the entry in row y and column x is psi(b x) when y = x + a and 0 otherwise. Here ite(c, u, v) is u if c holds and v otherwise.",
                "D", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("projector", "The orbit projectors", ProjectorFormula(),
                "Pi_{a,b} = D_{a,b} |phi><phi| D_{a,b}^dagger for g = (a, b), where vecMulVec(phi, star(phi)) is the outer product |phi><phi| and the superscript H is the conjugate transpose.",
                "proj", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("gram", "The projector Gram matrix", GramFormula(),
                "The q^2 x q^2 matrix with entries Tr(Pi_u Pi_v), indexed by pairs u, v in F(r) x F(r).",
                "gram", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("stable", "A lower bound for the nonidentity floor", StableFormula(),
                "StableWith(phi, c) says that the Hermitian form of the projector Gram matrix is at least c times the squared norm on every vector w whose entries sum to zero, the orthogonal complement of the constant vector. This is the Rayleigh-quotient form of lambda(phi) >= c for the smallest nonidentity eigenvalue lambda(phi).",
                "StableWith", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Uniform stability in characteristic three", ClaimFormula(),
                "A constant c > 0 and, for every r >= 1, a unit vector phi in C^{F(r)} with lambda(phi) >= c q/(q + 1), q = 3^r; equivalently eta(phi) = ((q + 1)/q) lambda(phi) >= c for every r, the uniform spectral stability of the paper in characteristic three.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Characteristic three has a uniformly stable family", Disp(F.Id("claim")),
                "Take c = 1/8, s = sqrt(q) and phi = (u + e_0)/sqrt(2 + 2/s) with u the normalized uniform vector. The ambiguity function A(a, b) = <phi, D_{a,b} phi> equals (delta_{b,0} + delta_{a,0} + (1 + psi(-a b))/s)/(2 + 2/s), because the character sums of psi over F(r) vanish at every nonzero frequency (the trace is a nonzero functional). Off the axes psi takes only the cube roots of unity, so |1 + psi| >= 1, and on the axes |A| = (s + 2)/(2(s + 1)); hence |A(h)|^2 >= 1/(4(s + 1)^2) for every h != 0. Expanding |phi><phi| in the orthogonal displacement basis and using the multiplication law of the displacements, the Gram form of w is (1/q) sum_h |A(h)|^2 |w^(h)|^2, where w^ is the symplectic Fourier transform of w; Parseval gives sum_h |w^(h)|^2 = q^2 sum_g |w(g)|^2, and w^(0) = sum_g w(g) = 0. So the form is at least q/(4(s + 1)^2) times the squared norm, and q/(4(s + 1)^2) >= (1/8) q/(q + 1) because 2(q + 1) - (s + 1)^2 = (s - 1)^2 >= 0.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhu-wang-2026-characteristic-three-uniform-stability"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("charthreewh-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula All(Formula a, Formula type, Formula body) =>
        Seq(Forall, Sp, a, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula a, Formula type, Formula body) =>
        Seq(Exists, Sp, a, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula PlusOf(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula TimesOf(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Power(Formula b, Formula e) => Seq(b, Caret, Grp(e));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula R() => F.Id("r");
    private static Formula Field() => Call("F", R());
    private static Formula Pairs() => Seq(Field(), Sp, Times, Sp, Field());
    private static Formula Vectors() => Seq(Field(), Sp, To, Sp, Complexes());
    private static Formula PairVectors() => Seq(Parenthesized(Pairs()), Sp, To, Sp, Complexes());
    private static Formula Apply(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Character(Formula x) => Apply(Psi, x);
    private static Formula Norm(Formula value) => Seq(Vert, Sp, value, Vert);
    private static Formula SumOver(Formula index, Formula body) => Seq(Sum, Underscore, Grp(index), Sp, body);
    private static Formula Phi() => Varphi;

    private static Formula FieldFormula() =>
        Disp(All(R(), Naturals(), Equal(Field(), Call("GaloisField", F.D(3), R()))));

    private static Formula CharacterFormula()
    {
        Formula x = F.Id("x");
        Formula trace = Call("val", Call("trace", Call("ZMod", F.D(3)), Field(), x));
        Formula phase = new Formula.Fraction(
            TimesOf(TimesOf(TimesOf(F.D(2), Pi), F.Id("i")), trace), F.D(3));
        return Disp(All(R(), Naturals(), All(x, Field(), Equal(Character(x), Call("exp", phase)))));
    }

    private static Formula DisplacementFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), x = F.Id("x"), y = F.Id("y");
        Formula entry = new Formula.Apply(Call("D", a, b), [y, x]);
        Formula value = Call("ite", Equal(y, PlusOf(x, a)), Character(TimesOf(b, x)), F.D(0));
        return Disp(All(R(), Naturals(), All(a, Field(), All(b, Field(), All(x, Field(), All(y, Field(),
            Equal(entry, value)))))));
    }

    private static Formula ProjectorFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b");
        Formula d = Call("D", a, b);
        Formula outer = Call("vecMulVec", Phi(), Call("star", Phi()));
        Formula value = TimesOf(TimesOf(d, outer), Power(d, F.Id("H")));
        return Disp(All(R(), Naturals(), All(Phi(), Vectors(), All(a, Field(), All(b, Field(),
            Equal(Call("proj", Phi(), Parenthesized(Seq(a, Comma, Sp, b))), value))))));
    }

    private static Formula GramFormula()
    {
        Formula u = F.Id("u"), v = F.Id("v");
        Formula entry = new Formula.Apply(Call("gram", Phi()), [u, v]);
        Formula value = Call("trace", TimesOf(Call("proj", Phi(), u), Call("proj", Phi(), v)));
        return Disp(All(R(), Naturals(), All(Phi(), Vectors(), All(u, Pairs(), All(v, Pairs(),
            Equal(entry, value))))));
    }

    private static Formula StableFormula()
    {
        Formula c = F.Id("c"), w = F.Id("w"), g = F.Id("g");
        Formula zeroSum = Equal(SumOver(g, Apply(w, g)), F.D(0));
        Formula normSq = SumOver(g, Power(Norm(Apply(w, g)), F.D(2)));
        Formula form = Call("Re", Call("dotProduct", Call("star", w), Call("mulVec", Call("gram", Phi()), w)));
        Formula bound = Leq(TimesOf(c, normSq), form);
        return Disp(All(R(), Naturals(), All(Phi(), Vectors(), All(c, Reals(),
            Iff(Call("StableWith", Phi(), c), All(w, PairVectors(), Implies(zeroSum, bound)))))));
    }

    private static Formula ClaimFormula()
    {
        Formula c = F.Id("c"), x = F.Id("x");
        Formula q = Power(F.D(3), R());
        Formula level = new Formula.Fraction(TimesOf(c, q), PlusOf(q, F.D(1)));
        Formula unit = Equal(SumOver(x, Power(Norm(Apply(Phi(), x)), F.D(2))), F.D(1));
        Formula family = All(R(), Naturals(), Implies(Leq(F.D(1), R()),
            Some(Phi(), Vectors(), And(unit, Call("StableWith", Phi(), level)))));
        return Disp(Iff(F.Id("claim"), Some(c, Reals(), And(Less(F.D(0), c), family))));
    }
}
