using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class GardamDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithUnits/Gardam.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/gardam2021unitconjecture");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gardam's exact Promislow group-ring counterexample over ZMod 2, transported through a faithful four-coset model.",
        H("Gardam's Unit-Conjecture Counterexample"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gardam-presented-torsion-free"),
                DeclarationHandle.Create(Prefix + "presented_torsion_free"),
                H("The presented group is torsion-free"),
                StatementSource.FromAuthor(TorsionFreeFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For the exact two-generator presentation from Gardam's Theorem A, every "
                        + "nonzero natural power that equals one forces the element to be one. "
                        + "The proof constructs and verifies a faithful four-coset normal form.")),
                    Paragraph(Text(
                        "This is the original-P supplier used by the final exact statement. The "
                        + "normal-form group, its action and factor set, and both inverse identities "
                        + "are retained in the Lean dependency path."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gardam-official-is-unit"),
                DeclarationHandle.Create(Prefix + "official_isUnit"),
                H("The official group-ring element is a unit"),
                StatementSource.FromAuthor(UnitFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The exact element u in the group ring F₂[P] is a unit. The certificate "
                        + "supplies an explicit inverse and checks both left and right products "
                        + "coefficient by coefficient in the four-coset model."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gardam-official-not-basis"),
                DeclarationHandle.Create(Prefix + "official_not_basis"),
                H("The unit is not a group basis element"),
                StatementSource.FromAuthor(NotBasisFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "No element of P equals u. Transport to the faithful normal form reduces "
                        + "this to the explicit 21-element support computation, so the nontrivial "
                        + "unit conclusion remains tied to the original presentation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gardam-two-sided-inverse"),
                DeclarationHandle.Create(Prefix + "mul_inverseE"),
                H("The explicit inverse works on both sides"),
                StatementSource.FromAuthor(InverseFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The four-coset certificate proves unitE * inverseE = 1; the companion "
                        + "inverseE_mul declaration proves the reverse product. These identities "
                        + "are consumed by official_isUnit."))),
                DescribeRole.Theorem))));

    private static Formula TorsionFreeFormula() => Disp(Seq(
            Forall, Sp, F.Id("g"), Sp, InMacro, Sp, F.Id("P"), Comma, Quad, Sp,
            Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Quad, Sp,
            F.Id("n"), Sp, Neq, Sp, D(0), Sp, Land, Sp,
            Seq(F.Id("g"), Caret, Grp(F.Id("n"))), Sp, Eq, Sp, D(1), Sp,
            Rightarrow, Sp, F.Id("g"), Sp, Eq, Sp, D(1)));

    private static Formula UnitFormula() => Disp(
        Seq(Operatorname, Grp(F.Id("IsUnit")), Sp, F.Id("u")));

    private static Formula NotBasisFormula() => Disp(Seq(
            Neg, Sp, Exists, Sp, F.Id("g"), Sp, InMacro, Sp, F.Id("P"), Comma, Quad, Sp,
            F.Id("u"), Sp, Eq, Sp, F.Id("g")));

    private static Formula InverseFormula() => Disp(Seq(
        F.Id("unitE"), Sp, Times, Sp, F.Id("inverseE"), Sp, Eq, Sp, D(1)));
}
