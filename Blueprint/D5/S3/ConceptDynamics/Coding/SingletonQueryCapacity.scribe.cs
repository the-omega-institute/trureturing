using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class SingletonQueryCapacityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adaptive singleton-or-constant binary questions identify at most d+1 sources at depth d.",
        H("Singleton-or-constant query capacity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("singleton-or-constant-query-capacity"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/SingletonQueryCapacity.singleton_or_constant_query_capacity"),
                H("Linear capacity for exact adaptive identification"),
                StatementSource.FromAuthor(CapacityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(DefinitionDsl.Text(
                        "Let X be any finite source type and let p be a BinaryProtocol of depth d. "
                        + "Write T for its transcript and q(t,h,x) for its question at round t, "
                        + "history h and source x. Transcript consistency means that the t-th bit "
                        + "of T(x) equals q(t,T(x) restricted to earlier rounds,x).")),
                    Paragraph(DefinitionDsl.Text(
                        "Assume T is injective. Every question, at every history including "
                        + "unrealized histories, is either constant on X or true at at most one "
                        + "source. Both constant false and constant true are permitted.")),
                    Paragraph(DefinitionDsl.Text(
                        "After t rounds, retain a set of sources sharing one transcript prefix "
                        + "and having size at least the size of X minus t. A constant answer keeps "
                        + "the entire set. For a question with at most one true source, keeping "
                        + "the false answers removes at most one member. Transcript consistency "
                        + "extends the common prefix. At depth d, injectivity leaves at most "
                        + "one member, giving the stated bound.")),
                    Paragraph(DefinitionDsl.Text(
                        "No nonemptiness or positive-depth assumption is imposed. Repeated "
                        + "constant YES answers are allowed; the last remaining candidate can "
                        + "be inferred without an additional question. The questions may depend "
                        + "on the complete previous history, and no prior source information is supplied."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula CapacityFormula()
    {
        Formula x = F.Id("x"), X = F.Id("X"), d = F.Id("d"), p = F.Id("p");
        Formula t = F.Id("t"), h = F.Id("h"), b = F.Id("b"), T = F.Id("T");
        Formula boolean = Seq(Operatorname, Grp(F.Id("Bool")));
        Formula q = Call("q", t, h, x);
        Formula constant = Seq(Open, Exists, Sp, b, Colon, Sp, boolean, Comma, Sp,
            Forall, Sp, x, Colon, Sp, X, Comma, Sp, q, Eq, b, Close);
        Formula support = Seq(OpenBrace, x, Colon, Sp, X, Sp, Mid, Sp,
            q, Eq, Operatorname, Grp(F.Id("true")), CloseBrace);
        return Disp(Seq(Begin, Grp(F.Id("gathered")),
            Forall, Sp, X, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            OpenBracket, Call("Fintype", X), CloseBracket, Comma, Sp,
            d, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            p, Colon, Sp, Call("BinaryProtocol", X, d), Comma, RowBreak, Grp(),
            Call("Injective", T), Sp, Land, Sp,
            OpenBracket, Forall, Sp, t, Colon, Sp, Call("Fin", d), Comma, Sp,
            Forall, Sp, h, Colon, Sp, Open, Call("Fin", Call("val", t)), Sp,
            To, Sp, boolean, Close, Comma, RowBreak, Grp(),
            constant, Sp, Lor, Sp, Call("card", support), Sp, Leq, Sp, D(1),
            CloseBracket, RowBreak, Grp(), Implies, Sp,
            Call("card", X), Sp, Leq, Sp, d, Plus, D(1), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
