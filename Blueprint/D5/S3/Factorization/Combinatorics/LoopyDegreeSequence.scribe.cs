using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Combinatorics;

internal sealed class LoopyDegreeSequenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/Combinatorics/LoopyDegreeSequence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/kirillov2026loopy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equality of ordinary Loopy polynomials determines the complete actual degree multiset.",
        H("Ordinary Loopy Equality Recovers Every Degree"),
        Blocks(
            Paragraph(Text(
                "The graph inputs are independent finite vertex sets, lists of edge occurrences and "
                + "accumulated-loop functions. Pending loops count twice through their two stored endpoints; "
                + "accumulated loops count twice explicitly. Mapping every retained vertex preserves isolates, "
                + "so degree zero remains part of the multiset.")),
            Def("incidence", "Incidence of one stored endpoint pair", "incidence",
                "incidence e v is the sum of the two endpoint equality indicators. A pending loop at v therefore contributes two."),
            Def("pending-degree", "Degree from pending occurrences", "pendingDegree",
                "pendingDegree folds incidence over the entire edge list, retaining the multiplicity of parallel edge occurrences."),
            Def("degree", "The actual graph-theoretic degree", "degree",
                "degree E ell v is 2*ell(v) plus pendingDegree E v. Both accumulated and pending loops count twice."),
            Def("degree-multiset", "The complete degree multiset", "degreeMultiset",
                "degreeMultiset maps degree E ell over the underlying multiset of V. It includes every retained vertex, hence isolates, and preserves multiplicity."),
            Def("geometric-sum", "Finite geometric sums", "geometricSum",
                "geometricSum h is the integer polynomial sum of t^i for 0 <= i < h."),
            Def("degree-specialization", "The degree-product specialization", "degreeSpecialization",
                "degreeSpecialization fixes the deletion variable and sends x_r to geometricSum(2*r+1). This substitution is proved effective in this repository; it is not attributed to source section 6.5."),
            Def("order-specialization", "The order specialization", "orderSpecialization",
                "orderSpecialization evaluates the deletion variable at one and sends every x_r to one common polynomial variable."),
            Describe.Lean(
                DescribeId.Create("loopy-degree-sequence-result"),
                DeclarationHandle.Create(Prefix + "loopy_determines_degree_multiset"),
                H("Ordinary Loopy equality determines the full degree multiset"),
                StatementSource.FromAuthor(EndpointFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For independent V, W, E, F, ell and eta, the only hypotheses are Valid V E ell, "
                        + "Valid W F eta and equality of the two ordinary Loopy polynomials. The conclusion "
                        + "is equality of the actual degree multisets. There is no equal-order, connectedness, "
                        + "nonemptiness, simplicity or looplessness premise.")),
                    Paragraph(Text(
                        "The live first induction gives P = product_v [degree(v)+1] after the new substitution "
                        + "x_r=[2r+1]. The live second induction makes U monic of degree |V| and derives the "
                        + "common order from Loopy equality. Thus q=(1-t)^n P is the product of "
                        + "1-t^(degree(v)+1). For c(r)=-count(degree=r), finite representation splits at "
                        + "d<N; k<=N and not d<N give k<d+1 for the omitted tail, including N=k=0. "
                        + "The frozen primitive Euler-ledger uniqueness theorem is then applied directly, "
                        + "and coordinate zero recovers isolates."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("loopy-degree-sequence-with-loops"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Def(string id, string title, string name, string prose) =>
        Describe.Lean(DescribeId.Create("loopy-degree-sequence-" + id),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(DefinitionFormula(name)),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula DefinitionFormula(string name) => name switch
    {
        "incidence" => Eqn(Call("incidence", I("e"), I("v")),
            Add(Indicator(Equal(App("fst", I("e")), I("v"))),
                Indicator(Equal(App("snd", I("e")), I("v"))))),
        "pendingDegree" => Disp(Seq(
            Equal(Call("pendingDegree", I("nil"), I("v")), D(0)), Comma, Sp,
            Equal(Call("pendingDegree", App("cons", I("e"), I("E")), I("v")),
                Add(Call("incidence", I("e"), I("v")),
                    Call("pendingDegree", I("E"), I("v")))))),
        "degree" => Eqn(Call("degree", I("E"), I("ell"), I("v")),
            Add(Multiply(D(2), Call("ell", I("v"))), Call("pendingDegree", I("E"), I("v")))),
        "degreeMultiset" => Eqn(Call("degreeMultiset", I("V"), I("E"), I("ell")),
            Call("map", Call("degree", I("E"), I("ell")), App("val", I("V")))),
        "geometricSum" => Eqn(Call("geometricSum", I("h")),
            Seq(Sum, Underscore,
                Grp(Seq(I("i"), Sp, InMacro, Sp, Call("range", I("h")))), Sp,
                Power(I("t"), I("i")))),
        "degreeSpecialization" => Disp(Seq(
            Equal(I("degreeSpecialization"),
                Call("eval2Hom", Call("id", App("Polynomial", I("Int"))),
                    Seq(I("r"), Sp, Mapsto, Sp,
                        Call("geometricSum", Add(Multiply(D(2), I("r")), D(1)))))),
            Comma, Sp,
            Equal(Call("degreeSpecialization", App("C", I("t"))), I("t")),
            Comma, Sp,
            Equal(Call("degreeSpecialization", App("x", I("r"))),
                Call("geometricSum", Add(Multiply(D(2), I("r")), D(1)))))),
        "orderSpecialization" => Disp(Seq(
            Equal(Call("orderSpecialization", App("C", I("t"))), D(1)), Comma, Sp,
            Equal(Call("orderSpecialization", App("x", I("r"))), I("z")))),
        _ => throw new ArgumentOutOfRangeException(nameof(name))
    };

    private static Formula EndpointFormula()
    {
        var nat = I("Nat");
        var vertices = App("Finset", nat);
        var edges = App("List", I("Edge"));
        var loops = Seq(nat, Sp, To, Sp, nat);
        var conclusion = Equal(
            Call("degreeMultiset", I("V"), I("E"), I("ell")),
            Call("degreeMultiset", I("W"), I("F"), I("eta")));
        var hypotheses = Implies(Call("Valid", I("V"), I("E"), I("ell")),
            Implies(Call("Valid", I("W"), I("F"), I("eta")),
                Implies(Equal(Call("loopy", I("V"), I("E"), I("ell")),
                    Call("loopy", I("W"), I("F"), I("eta"))), conclusion)));
        return Disp(All("V", vertices, All("W", vertices, All("E", edges, All("F", edges,
            All("ell", loops, All("eta", loops, hypotheses)))))));
    }

    private static Formula I(string value) => F.Id(value);
    private static Formula Named(string value) => Seq(Operatorname, Grp(I(value)));
    private static Formula App(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(name, args);
    private static Formula Eqn(Formula left, Formula right) => Disp(Equal(left, right));
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) => Seq(left, Sp, Plus, Sp, right);
    private static Formula Multiply(Formula left, Formula right) => Seq(left, Sp, Cdot, Sp, right);
    private static Formula Power(Formula value, Formula exponent) => Seq(value, Caret, Grp(exponent));
    private static Formula Indicator(Formula predicate) =>
        Seq(OpenBracket, predicate, CloseBracket);
    private static Formula Implies(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Rightarrow, Sp, Open, right, Close);
    private static Formula All(string variable, Formula type, Formula body) =>
        Seq(Forall, Sp, I(variable), Colon, Sp, type, Comma, Sp, body);
}
