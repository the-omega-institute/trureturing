using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Naturality;

internal sealed class InvariantOriginRecoveryObstructionDocument : IScribeDocumentDefinition
{
    private const string Gid =
        "D5/S3/Observer/Naturality/InvariantOriginRecoveryObstruction."
        + "no_absolute_origin_reconstruction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A transitive invariant readout cannot recover or duplicate a nontrivial origin.",
        H("Invariant Origin Recovery Obstruction"),
        Blocks(Describe.Lean(
            DescribeId.Create("no-absolute-origin-reconstruction"),
            DeclarationHandle.Create(Gid),
            H("No absolute-origin reconstruction"),
            StatementSource.FromAuthor(StatementFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A group G acts transitively on a nontrivial origin type A. The internal "
                        + "readout q is invariant under that action, so every two origins have "
                        + "the same internal description.")),
                Paragraph(Text(
                    "The declaration rules out both a left-inverse decoder and a duplicator "
                        + "that would return the ordered pair (a,a) from q(a). It also exposes "
                        + "two distinct origins with equal readout, retaining the relational "
                        + "coordinate distinction in the public statement."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula StatementFormula()
    {
        Formula group = F.Id("G");
        Formula origin = F.Id("A");
        Formula output = F.Id("Y");
        Formula type = F.Id("Type");
        Formula readout = F.Id("q");
        Formula g = F.Id("g");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula decoder = F.Id("d");
        Formula duplicate = F.Id("C");
        Formula smul = Call("smul", g, a);
        Formula invariant = Seq(
            Forall, Sp, Typed(g, group), Comma, Sp, Typed(a, origin), Comma, Sp,
            Apply(readout, smul), Sp, Eq, Sp, Apply(readout, a));
        Formula sameReadout = Seq(
            Forall, Sp, Typed(Seq(a, Comma, Sp, b), origin), Comma, Sp,
            Apply(readout, a), Sp, Eq, Sp, Apply(readout, b));
        Formula noDecoder = Seq(
            Neg, Sp, Exists, Sp, Typed(decoder, Arrow(output, origin)), Comma, Sp,
            Call("LeftInverse", decoder, readout));
        Formula originPair = Seq(origin, Sp, Times, Sp, origin);
        Formula noDuplicator = Seq(
            Neg, Sp, Exists, Sp, Typed(duplicate, Arrow(output, originPair)), Comma, Sp,
            Forall, Sp, Typed(a, origin), Comma, Sp,
            Apply(duplicate, Apply(readout, a)), Sp, Eq, Sp,
            Open, a, Comma, Sp, a, Close);
        Formula distinctPair = Seq(
            Exists, Sp, Typed(Seq(a, Comma, Sp, b), origin), Comma, Sp,
            a, Sp, Neq, Sp, b, Sp, Land, Sp,
            Apply(readout, a), Sp, Eq, Sp, Apply(readout, b));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(Seq(group, Comma, Sp, origin, Comma, Sp, output), type),
            Comma, RowBreak, Grp(),
            Call("Group", group), Sp, Land, Sp, Call("MulAction", group, origin),
            Sp, Land, Sp, Call("IsPretransitive", group, origin), Sp, Land, Sp,
            Call("Nontrivial", origin), Comma, RowBreak, Grp(),
            Forall, Sp, Typed(readout, Arrow(origin, output)), Comma, Sp,
            Open, invariant, Close, Sp, Rightarrow, RowBreak, Grp(),
            Open, sameReadout, Close, Sp, Land, RowBreak, Grp(),
            Open, noDecoder, Close, Sp, Land, RowBreak, Grp(),
            Open, noDuplicator, Close, Sp, Land, RowBreak, Grp(),
            Open, distinctPair, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
