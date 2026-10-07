using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class PassiveQueryMemoizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Memoizing a passive dependent protocol charges each actual address once and preserves completed-history equality.",
        H("Passive Query Memoization"),
        Blocks(Describe.Lean(
            DescribeId.Create("uniform-passive-query-memoization"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Experiment/PassiveQueryMemoization.result"),
            H("Uniform memoization of the original dependent tree"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let Q and W be arbitrary types, let Y(q) be a dependent response family, "
                    + "and fix read(q): W to Y(q). The original PassiveProtocol T is a well-founded "
                    + "dependent tree, executed by runPassiveProtocol on the same source throughout.")),
                Paragraph(Text("A cache K is a dependent partial function assigning an optional response to each q. "
                    + "The structural transform memo(T,K) leaves stop unchanged. A hit follows the original "
                    + "continuation at the cached response without querying. A miss retains the original query "
                    + "and updates K with each possible response inside that response continuation. "
                    + "The empty-cache tree M(T) is selected from T alone, before W, read, or the source.")),
                Paragraph(Text("Write h(x) for the original completed history and m(x) for the actual history of M(T). "
                    + "Let addr project each dependent query-response pair to its query. Then m(x) is a Sublist "
                    + "of h(x), addr(m(x)) has no repetitions, and their address supports are equal. "
                    + "Thus the length of m(x) equals the cardinality of the finite address support of h(x). "
                    + "For all x and y, m(x)=m(y) if and only if h(x)=h(y).")),
                Paragraph(Text("The proof follows the original response-selected continuation with an arbitrary cache "
                    + "coherent with the source. Its strengthened induction keeps the paid suffix inside the old "
                    + "suffix, makes its addresses distinct and absent from the initial cache, and covers every "
                    + "old address by the initial cache or the paid suffix. Actual pair consistency and exact "
                    + "address support then allow the original execution-transfer and monotonicity results "
                    + "to establish both directions of completed-history equality.")),
                Paragraph(Text("There is no finite or inhabited carrier premise, response equality test, common "
                    + "fuel bound, or replacement oracle. Empty types and infinite response families remain "
                    + "in scope; different responses can lead to arbitrarily long finite branches. "
                    + "A fresh query with a constant response is retained. The result concerns passive fixed "
                    + "readouts and provides no arithmetic support bound, optimality theorem, or bound for active actions."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula m = Call("m", x);
        Formula h = Call("h", x);
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, x, Comma, Sp, Call("Sublist", m, h), Land,
                Call("Nodup", Call("addr", m)), Comma),
            Seq(Call("support", Call("addr", m)), Eq, Call("support", Call("addr", h)), Comma),
            Seq(Call("length", m), Eq, Call("card", Call("support", Call("addr", h))), Comma),
            Seq(Forall, Sp, x, Comma, y, Comma, Sp, Call("m", x), Eq, Call("m", y),
                Leftrightarrow, Sp, Call("h", x), Eq, Call("h", y), Dot)
        ]));
    }
}
