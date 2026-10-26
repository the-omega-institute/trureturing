using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class LegalFiberReconstructionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/LegalFiberReconstruction.";
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Nat => Call("Nat");
    private static Formula Digits => Call("LegalDigits");
    private static Formula N => V("n");
    private static Formula Next => Seq(N, Plus, Num(1));
    private static Formula Pref(Formula p, Formula n) => Call("legalPrefix", p, n);
    private static Formula P(Formula n) => Call("Prefix", n);
    private static Formula K(Formula n, Formula s) => Call("K", n, s);
    private static Formula LambdaN(Formula body) => Seq(N, Sp, Mapsto, Sp, body);
    private static Formula Child => All("i", Call("Fin", N),
        Equal(Call("t", Call("castSucc", V("i"))), Call("s", V("i"))));
    private static Formula Cover => All("n", Nat, All("s", P(N), All("x", V("X"),
        Iff(Mem(V("x"), K(N, V("s"))), Ex("t", P(Next),
            And(Child, Mem(V("x"), K(Next, V("t")))))))));
    private static Formula Shrink => All("p", Digits, Call("Tendsto",
        Grp(LambdaN(Call("diam", K(N, Pref(V("p"), N))))), Call("atTop"), Call("nhds", Num(0))));
    private static Formula Graph => All("p", Digits, All("x", V("X"),
        Iff(Equal(Call("f", V("p")), V("x")), All("n", Nat,
            Mem(V("x"), K(N, Pref(V("p"), N)))))));
    private static Formula Statement => Disp(new Formula.Aligned([
        Seq(Forall, Sp, V("X"), Colon, Sp, Call("Type", V("u")), Comma, Sp,
            OpenBracket, Call("MetricSpace", V("X")), CloseBracket, Sp,
            OpenBracket, Call("CompactSpace", V("X")), CloseBracket, Comma),
        Seq(Forall, Sp, V("K"), Colon, Sp,
            Open, N, Colon, Sp, Nat, Close, Sp, To, Sp,
            Fn(P(N), Call("Set", V("X"))), Comma),
        Imp(And(All("n", Nat, All("s", P(N), Call("Nonempty", K(N, V("s"))))),
            And(All("n", Nat, All("s", P(N), Call("IsCompact", K(N, V("s"))))),
            And(Equal(K(Num(0), Pref(Call("zero"), Num(0))), Call("univ", V("X"))),
            And(Cover, Shrink)))),
            Ex("f", Fn(Digits, V("X")), And(Call("Continuous", V("f")),
                And(Call("Surjective", V("f")), Graph))))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonempty compact fibers indexed by legal Boolean prefixes reconstruct a continuous surjection when their real diameters vanish along each legal branch.",
        H("Reconstruction from legal nested fibers"), Blocks(
            Paragraph(Text("LegalDigits is the existing space of functions from the natural numbers to Bool with no adjacent true entries, with its product subspace topology. "
                + "Prefix(n) consists exactly of functions w from Fin(n) to Bool for which some p in LegalDigits satisfies p(i)=w(i) at every i<n. "
                + "The function legalPrefix(p,n) restricts p to indices zero through n minus one. The symbol zero denotes the all-false legal stream. "
                + "There is one prefix at level zero. A child t at level n+1 agrees with its parent s through castSucc, the inclusion of Fin(n) into Fin(n+1). "
                + "Thus the coverage equivalence in the theorem is exactly equality with the union of all legal child fibers.")),
            Describe.Lean(DescribeId.Create("continuous-reconstruction"),
                DeclarationHandle.Create(Owner + "continuous_reconstruction"),
                H("Unique reconstruction and existence of names"), StatementSource.FromAuthor(Statement),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The type X is any compact metric space, at arbitrary universe level u. All nonemptiness and compactness assumptions range over legal prefixes only. "
                        + "Diameter is real-valued; compactness supplies the boundedness needed by the distance estimate. Shrinking is quantified separately for each legal infinite branch. "
                        + "The map f is continuous and onto, and its value is the unique point belonging to every fiber on that branch, including the root. "
                        + "Different names may represent the same point. Child fibers may overlap. No uniform shrinking rate or effective selection algorithm is asserted.")),
                    Paragraph(Text("Child coverage makes each branch decreasing. Cantor's compact intersection theorem supplies a point in its full intersection. "
                        + "The distance between any two such points is bounded by every branch diameter, so it is zero. "
                        + "For a prescribed point x, choose successively a legal child whose fiber still contains that same x. "
                        + "The selected finite words agree on every earlier coordinate. Their diagonal entries define a stream, and every selected word is its exact restriction. "
                        + "Its adjacent entries occur together in a legal finite word, so this stream is an element of LegalDigits. It names x.")),
                    Paragraph(Text("At a fixed name p, choose a prefix whose fiber diameter is below the desired positive error. All names agreeing with p on this finite prefix form a neighborhood. "
                        + "Their reconstructed points lie in the same fiber, proving continuity without a uniform convergence hypothesis. "
                        + "The compact-intersection supplier is IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed; the real metric estimate is Metric.dist_le_diam_of_mem. "
                        + "These classical results are applied directly. The legal-prefix construction uses the existing LegalDigits representation."))), DescribeRole.Theorem))));
}
