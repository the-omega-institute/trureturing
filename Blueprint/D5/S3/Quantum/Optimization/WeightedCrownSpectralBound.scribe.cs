using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Optimization;

internal sealed class WeightedCrownSpectralBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Optimization/WeightedCrownSpectralBound.";

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumBounds/takahashietal2023su2sdp");
    private static readonly Formula N = F.Id("n"), I = F.Id("i"), J = F.Id("j"), K = F.Id("k"), X = F.Id("x");
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Index() => Call("Option", Call("Option", Call("Fin", N)));
    private static Formula Basis() => new Formula.TypeArrow(Index(), Call("Fin", D(2)));
    private static Formula Mat(Formula index, Formula field) => Call("Matrix", index, index, field);
    private static Formula Cast(Formula a, Formula t) => Parenthesized(Seq(a, Colon, t));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Qualified(string owner, string name)
    {
        var parts = owner.Split('.').Append(name).ToArray();
        Formula result = Seq(Operatorname, Grp(F.Id(parts[0])));
        foreach (var part in parts.Skip(1)) result = Seq(result, Dot, Operatorname, Grp(F.Id(part)));
        return result;
    }
    private static Formula QCall(string owner, string name, params Formula[] args) => App(Qualified(owner, name), args);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(name, Colon, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Smul(Formula a, Formula b) => Seq(Parenthesized(a), Cdot, Parenthesized(b));
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula ProdOver(Formula v, Formula t, Formula body) => Seq(new Formula.Subscript(Prod, Seq(v, Colon, t)), Parenthesized(body));
    private static Formula If(Formula p, Formula a, Formula b) => Call("ite", p, a, b);
    private static Formula OverN(Formula f) => All(N, Nat(), f);
    private static Formula Sing(Formula i, Formula j) => Call("singlet", i, j);
    private static Formula PauliX() => Qualified("FiniteDimensional", "qubitX");
    private static Formula PauliZ() => Qualified("FiniteDimensional", "qubitZ");
    private static Formula PauliY() => Smul(Qualified("Complex", "I"), Mul(PauliX(), PauliZ()));
    private static Formula Site(Formula i, Formula a) => Call("site", i, a);
    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("weighted-crown-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role);

        private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Some(Formula name, Formula type, Formula body) => Seq(Exists, Sp, Parenthesized(Seq(name, Colon, type)), Comma, Sp, body);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula SumOver(Formula v, Formula t, Formula body) => Seq(new Formula.Subscript(Sum, Seq(v, Colon, t)), Parenthesized(body));
    private static Formula OverNX(Formula f) => OverN(All(X, Real(), f));
    private static Formula Hamiltonian() => Call("crownH", N, X);

public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The singlet-sector and star bounds control the literal crown Hamiltonian.",
        H("Weighted crown spectral bound"), Blocks(
            Node("a", "Crown vertex a", OverN(Eq(Call("a", N), F.Id("none"))),
                "Appendix C.1, p. 33: \"Note that the n + 2 vertices in total are labeled as a, b, 1, 2, 3, . . . , n and we assume n \u2265 3.\" The two Option constructors distinguish the hubs and the n leaves.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("b", "Crown vertex b", OverN(Eq(Call("b", N), Call("some", F.Id("none")))),
                "Appendix C.1, p. 33: \"Note that the n + 2 vertices in total are labeled as a, b, 1, 2, 3, . . . , n and we assume n \u2265 3.\" The two Option constructors distinguish the hubs and the n leaves.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("leaf", "Crown vertex leaf", OverN(All(I, Call("Fin", N), Eq(Call("leaf", I), Call("some", Call("some", I))))),
                "Appendix C.1, p. 33: \"Note that the n + 2 vertices in total are labeled as a, b, 1, 2, 3, . . . , n and we assume n \u2265 3.\" The two Option constructors distinguish the hubs and the n leaves.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("site", "A matrix acting at one site", OverN(All(I, Index(), All(F.Id("A"), Mat(Call("Fin", D(2)), Complex()), All(F.Id("s"), Basis(), All(F.Id("t"), Basis(), Eq(App(Call("site", I, F.Id("A")), F.Id("s"), F.Id("t")), ProdOver(K, Index(), If(Eq(K,I), App(F.Id("A"), App(F.Id("s"), K), App(F.Id("t"), K)), If(Eq(App(F.Id("s"),K),App(F.Id("t"),K)), D(1),D(0)))))))))),
                "The computational-basis entry is the product of the local matrix entry at i and identity entries at all other sites. This is the tensor action used in the singlet definition.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("singlet", "The singlet projection", OverN(All(I, Index(), All(J, Index(), Eq(Sing(I,J), Smul(Div(Cast(D(1),Complex()),Cast(D(4),Complex())), Sub(Sub(Sub(D(1), Mul(Site(I,PauliX()), Site(J,PauliX()))), Mul(Site(I,PauliY()),Site(J,PauliY()))), Mul(Site(I,PauliZ()),Site(J,PauliZ())))))))),
                "The source projector is (1 - X_i X_j - Y_i Y_j - Z_i Z_j)/4. FiniteDimensional.qubitX and qubitZ are the Pauli owners; Y is the inline expression Complex.I \u2022 (qubitX * qubitZ).", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a_ne_leaf", "The first hub differs from every leaf", OverN(All(I, Call("Fin", N), Ne(Call("a", N), Call("leaf", I)))),
                "The two hubs and the leaves are distinct vertices in Appendix C.1's labeling.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("b_ne_leaf", "The second hub differs from every leaf", OverN(All(I, Call("Fin", N), Ne(Call("b", N), Call("leaf", I)))),
                "The two hubs and the leaves are distinct vertices in Appendix C.1's labeling.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("crownH", "The weighted crown Hamiltonian", OverNX(Eq(Hamiltonian(), Add(Smul(Cast(X,Complex()),Sing(Call("a",N),Call("b",N))),SumOver(I,Call("Fin",N),Add(Sing(Call("a",N),Call("leaf",I)),Sing(Call("b",N),Call("leaf",I))))))),
                "Appendix C.1, p. 33, Eq. (C1): H = x h_ab + sum from j = 1 to n of (h_aj + h_bj). The coefficient x is cast from real to complex and the n spokes are counted once.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("lambdaMax", "The largest Rayleigh value", All(F.Id("iota"),F.Id("Type"),Seq(OpenBracket,Call("Fintype",F.Id("iota")),CloseBracket,All(F.Id("H"),Mat(F.Id("iota"),Complex()),Eq(Call("lambdaMax",F.Id("H")),Call("sSup",Seq(OpenBrace,F.Id("r"),Colon,Real(),Mid,Some(F.Id("v"),Call("EuclideanSpace",Complex(),F.Id("iota")),And(Ne(F.Id("v"),D(0)),Eq(F.Id("r"),Div(App(Qualified("Complex","re"), SumOver(I,F.Id("iota"),Mul(Call("star",App(F.Id("v"),I)), App(QCall("Matrix","mulVec",F.Id("H"),F.Id("v")),I)))),Pow(new Formula.Norm(F.Id("v")),D(2)))))),CloseBrace)))))),
                "The largest value is the real supremum of nonzero-vector Rayleigh quotients. For the Hermitian crown Hamiltonian, this supremum is the largest eigenvalue.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("crown_spectral_bound", "The crown spectral bound", OverNX(Imp(Le(X,Add(D(1),Div(Cast(N,Real()),D(2)))), Le(Call("lambdaMax",Hamiltonian()),Add(Cast(N,Real()),D(1))))),
                "The star-square relation bounds each hub star by (n+1)/2. The hub singlet is a projection P with PK = KP = (n/2)P. The identity (n+1)I-H = (I-P)((n+1)I-K)(I-P)+(1+n/2-x)P is positive semidefinite on the displayed range. P and K here describe the singlet and the sum of the two stars.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)))));
}
