using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer;

internal sealed class WindowCharacterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Nontrivial finite window matrix algebras have no complex-algebra character.",
        H("Absence of Characters on Nontrivial Finite Windows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nontrivial-finite-window-algebras-have-no-character"),
                DeclarationHandle.Create("D5/S3/Observer/WindowCharacter.window_algebra_has_no_character"),
                H("Nontrivial finite window algebras have no character"),
                StatementSource.FromAuthor(NoCharacterFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let M be a window cardinality greater than one, and suppose that phi is " +
                        "a unital complex-algebra homomorphism from the M-by-M window matrix " +
                        "algebra to the complex numbers. Applying phi to the finite Weyl " +
                        "relation and using commutativity of the target gives " +
                        "(1 - omega_M) phi(V_M) phi(U_M) = 0.")),
                    Paragraph(Text(
                        "The window phase is a primitive M-th root. Since M is greater than one, " +
                        "omega_M is not one, so the two generator images have zero product. On " +
                        "the other hand, the M-th powers of both window generators are the " +
                        "identity. Their images therefore have M-th power one and are both " +
                        "nonzero, a contradiction. The strict inequality on M supplies exactly " +
                        "the nontriviality of the primitive phase; no statement is made here for " +
                        "a one-address window or for matrix algebras with unrelated index sets."))),
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

    private static Formula NoCharacterFormula() => Disp(Seq(
        Forall, Sp, F.Id("M"), Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(1)), Comma, Esc,
        OpenBracket, Call("NeZero", F.Id("M")), CloseBracket, Comma, Esc,
        Operatorname, Grp(F.Id("IsEmpty")), Open,
        F.Id("M"), Underscore, Grp(F.Id("M")), Open,
        Mathbb, Grp(F.Id("C")), Close,
        To, Underscore, Grp(Mathbb, Grp(F.Id("C")), F.Text,
        Grp(Minus, F.Id("alg"))), Mathbb, Grp(F.Id("C")), Close));
}
