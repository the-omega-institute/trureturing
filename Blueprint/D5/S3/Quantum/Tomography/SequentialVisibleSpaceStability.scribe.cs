using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class SequentialVisibleSpaceStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A stable sequential word-effect span remains stable at every later depth.",
        H("Permanent Stability of Sequential Visible Spaces"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sequential-visible-space-stability"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/SequentialVisibleSpaceStability."
                        + "sequential_visible_space_once_stable_permanently"),
                H("One stable sequential stage is permanently stable"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The branch alphabet indexes real-linear Heisenberg dual maps on the "
                            + "full Hermitian matrix carrier. Each finite word effect is the "
                            + "existing source-order fold of those maps applied to identity.")),
                    Paragraph(Text(
                        "At depth k the visible space is stated directly as the real span of "
                            + "all word effects of length at most k. No parallel visible-space "
                            + "definition is introduced.")),
                    Paragraph(Text(
                        "Consecutive-stage equality makes the stable span invariant under every "
                            + "branch dual. Word induction then puts every longer effect in that "
                            + "span, while the depth inequality supplies the reverse inclusion."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Visible(
        Formula real,
        Formula alphabet,
        Formula instrumentDual,
        Formula bound)
    {
        Formula word = F.Id("w");
        Formula generated = Seq(
            OpenBrace,
            Call("sequentialWordEffect", instrumentDual, word), Sp, Mid, Sp,
            word, Colon, Sp, Call("List", alphabet), Comma, Sp,
            Call("length", word), Sp, Le, Sp, bound,
            CloseBrace);
        return Call("span", real, generated);
    }

    private static Formula TheoremFormula()
    {
        Formula dimension = F.Id("d");
        Formula alphabet = F.Id("A");
        Formula instrumentDual = F.Id("J");
        Formula stableDepth = F.Id("n");
        Formula laterDepth = F.Id("m");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula carrier = Call("HermitianSpace", dimension);
        Formula linearMap = Call("LinearMap", real, carrier, carrier);
        Formula stable = Visible(real, alphabet, instrumentDual, stableDepth);
        Formula successor = Visible(
            real, alphabet, instrumentDual, Seq(stableDepth, Plus, D(1)));
        Formula later = Visible(real, alphabet, instrumentDual, laterDepth);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, dimension, Colon, Sp, F.Id("Nat"), Comma, Sp,
            alphabet, Colon, Sp, type, Comma, RowBreak, Grp(),
            instrumentDual, Colon, Sp, Arrow(alphabet, linearMap), Comma, Sp,
            stableDepth, Colon, Sp, F.Id("Nat"), Comma, RowBreak, Grp(),
            successor, Sp, Eq, Sp, stable, Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, laterDepth, Colon, Sp, F.Id("Nat"), Comma, Sp,
            stableDepth, Sp, Le, Sp, laterDepth, Sp, Rightarrow, Sp,
            later, Sp, Eq, Sp, stable, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
