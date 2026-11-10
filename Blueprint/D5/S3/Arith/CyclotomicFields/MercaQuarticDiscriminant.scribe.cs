using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CyclotomicFields;

internal sealed class MercaQuarticDiscriminantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CyclotomicFields/MercaQuarticDiscriminant.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/mazhang2026quartic");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual maximal-order ramification, tame different and discriminant of the Merca cyclic quartic field.",
        H("The Actual Merca Quartic Discriminant"),
        Blocks(
            Paragraph(Text("For a prime r congruent to five modulo eight, lift maximal-order primes of the actual quartic fixed field to the ambient prime cyclotomic field. Unique total ramification upstairs and the inertia-degree tower give one prime downstairs with inertia degree one and ramification index four. The tame different has exact multiplicity three. Discriminant divisibility confines its support to r, and the CM signature fixes the positive sign.")),
            Node("prime-structure", "Actual ramification above r", "prime_structure",
                "There is one actual maximal-order prime above r, with e=4 and f=1. The proof does not assume that two generates the full unit group."),
            Node("different", "Actual different ideal", "different_eq",
                "The genuine absolute different ideal is the cube of that prime. The lower different bound and the tame upper bound apply to the actual finite residue fields; r does not divide four."),
            Node("discriminant", "Genuine quartic field discriminant", "discriminant",
                "The actual number-field discriminant is r cubed. The norm of the different gives its absolute value and the two complex places give its positive sign."),
            Paragraph(Text("This is a structural input to the relative ideal-class-number proof. It supplies no assumed class-number identity, signed quadratic L-value or complete MMZ criterion. Source-owner four-slot audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629. No declared_validated status is claimed.")),
            Paragraph(Text("Historical statement: Haobo Ma and Wenlin Zhang, CC BY 4.0. Classical cyclotomic ramification and the existing Dedekind tame-different supplier are reused. Louboutin, Hudson and the classical class-number sources retain their attribution; no novelty or priority claim is made.")))));
    private static DocumentBlock Node(string id, string title, string name, string text) =>
        Describe.Lean(DescribeId.Create("merca-quartic-discriminant-" + id),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
