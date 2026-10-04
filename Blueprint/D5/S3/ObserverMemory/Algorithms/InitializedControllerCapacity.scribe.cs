using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class InitializedControllerCapacityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniformly bounded cumulative communication forces sharp finite embeddings into every actual persistent readout fiber.",
        H("Necessary persistent controller capacities"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("initialized-controller-capacity"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Algorithms/InitializedControllerCapacity."
                    + "initialized_controller_capacity"),
                H("Fiber, local and joint lower embeddings without finite competitors"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix d at least two and a complementary pair A,B of positive "
                        + "dimensions in Source(d). Their control restrictions are ellA,ellB; "
                        + "rank means the dimension of the corresponding linear-map range. "
                        + "All universe levels u,v,w are arbitrary. The compliant controller has arbitrary local and root types. One "
                        + "natural K bounds all initialized finite-word cumulative costs.")),
                    Paragraph(Text(
                        "The theorem produces an injection of a finite set of size "
                        + "1+2^rank(ellB) into every left readout fiber and the symmetric "
                        + "injection into every right fiber. It also produces finite "
                        + "injections of the summed fiber capacities into both local "
                        + "carriers and of 2^(d+2) points into the operational joint carrier. "
                        + "No natural cardinality is taken of an infinite competitor.")),
                    Paragraph(Text(
                        "The already proved maximal-cost supplier gives one actual silent "
                        + "successor region covering every source. A paid rewrite has an "
                        + "internal root at every initialization and a leaf throughout that "
                        + "region, so each silent local state differs from every initial "
                        + "local state. Root agreement gives the same separation on both sides.")),
                    Paragraph(Text(
                        "When the opposite control restriction is nonzero, a nonzero "
                        + "projected data column exists because the data subspace projects "
                        + "onto the nonzero local summand. Two selected actual silent states "
                        + "with equal local state use the same local leaf update and empty "
                        + "bit string for that rewrite. Their required outputs therefore "
                        + "force their current controls to agree. The proof never splices "
                        + "endpoints from different actual states.")),
                    Paragraph(Text(
                        "Index the silent representatives in a fixed fiber by the range "
                        + "of the opposite control map and add one separate initial point. "
                        + "Readouts distinguish different fibers. Initial representatives "
                        + "and source-covering silent representatives give two disjoint "
                        + "joint copies of Source(d). Pinned finite vector-space cardinality "
                        + "and finite-set equivalence APIs convert these constructions into "
                        + "the displayed finite domains."))),
                DescribeRole.Theorem))));


    private static Formula V(string name) => F.Id(name);
    private static Formula P(Formula body) => Seq(Open, body, Close);
    private static Formula C(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Sp, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula A(params Formula[] clauses)
    {
        var items = new List<Formula>();
        foreach (var clause in clauses)
        {
            if (items.Count > 0) items.Add(Land);
            items.Add(P(clause));
        }
        return Seq([.. items]);
    }
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, type, Comma, P(body));
    private static Formula Imp(Formula premise, Formula body) =>
        Seq(P(premise), Implies, Sp, P(body));
    private static Formula E(Formula left, Formula right) => Seq(left, Eq, right);
    private static Formula LE(Formula left, Formula right) => Seq(left, Le, Sp, right);
    private static Formula LT(Formula left, Formula right) => Seq(left, Lt, right);
    private static Formula Pow(Formula left, Formula right) => Seq(left, Caret, Grp(right));
    private static Formula Ty(string level) => Seq(V("Type"), Underscore, Grp(V(level)));
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Bit => C("ZMod", D(2));

    private static Formula ResultFormula()
    {
        Formula d = V("d"), a = V("A"), b = V("B"), h = V("h"), c = V("C");
        Formula ma = V("MA"), mb = V("MB"), root = V("Root");
        Formula size(Formula other) => Seq(D(1), Plus,
            Pow(D(2), C("finrank", Bit, C("range", C("ell", other)))));
        Formula embedding(Formula n, Formula target) =>
            C("Nonempty", C("Embedding", C("Fin", n), target));
        Formula fiber(Formula carrier, string read, Formula value) => Seq(OpenBrace,
            V("m"), Colon, carrier, Mid, Sp, E(C(read, c, V("m")), value), CloseBrace);
        Formula result = A(
            All("a", a, embedding(size(b), fiber(ma, "readA", V("a")))),
            All("b", b, embedding(size(a), fiber(mb, "readB", V("b")))),
            embedding(Seq(P(size(b)), Times, Sp, Pow(D(2), C("finrank", Bit, a))), ma),
            embedding(Seq(P(size(a)), Times, Sp, Pow(D(2), C("finrank", Bit, b))), mb),
            embedding(Pow(D(2), Seq(d, Plus, D(2))), C("State", c)));
        return Disp(All("d", N, Imp(LE(D(2), d),
            All("A", C("Submodule", Bit, C("Source", d)),
            All("B", C("Submodule", Bit, C("Source", d)), All("h", C("IsCompl", a, b),
            Imp(A(LT(D(0), C("finrank", Bit, a)), LT(D(0), C("finrank", Bit, b))),
            All("MA", Ty("u"), All("MB", Ty("v"), All("Root", Ty("w"),
            All("C", C("Controller", h, ma, mb, root), All("K", N,
                Imp(C("UniformCumulativeBudget", c, V("K")), result)))))))))))));
    }
}
