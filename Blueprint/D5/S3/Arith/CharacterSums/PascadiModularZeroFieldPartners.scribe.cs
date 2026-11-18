using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiModularZeroFieldPartnersDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The formal cubic pencil identity has at most six ordered field-coordinate partners when both direction determinants are nonzero. This field classification is consumed by the actual bounded integer partner count; it does not by itself count original six-tuples.",
        H("Field geometry of nondividing modular-zero partners"),
        Blocks(
            Paragraph(Text("For the identity L_d L_z L_v=(L_z+L_v-L_q)L_a L_b with d=a+b-q, assume det(a,d) and det(d,b) are nonzero. Zero endpoints give only (0,q) and (q,0). Otherwise perpendicular evaluation and formal cancellation put the two endpoints on the a-line and b-line, in one of the two orientations. Writing z=ka and v=lb gives (kl-1)d=(k-1)a+(l-1)b. Determinants force either k=l=1 or the displayed nondividingLambda and nondividingMu. The argument retains proportional a,b and characteristic two.")),
            Paragraph(Text("The determinant and its scalar-collinearity lemma are also used by the regular dividing branch. The two explicit candidate scalars are shared with the finite field-pair set in PascadiModularZeroPartners. The passage from six field-coordinate pairs to at most six actual integer pairs uses full coordinate reduction on the bounded box in that importing module; no injectivity of a single shifted linear observation is asserted.")),
            Describe.Lean(DescribeId.Create("pascadi-modular-zero-field-det"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners.fieldDet"), H("fieldDet"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The homogeneous determinant over a commutative coefficient ring."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pascadi-modular-zero-field-scalar"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners.fieldDet_zero_scalar"), H("Collinearity gives a scalar"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Over a field, a vector with zero determinant against a nonzero vector is a scalar multiple of it."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-modular-zero-field-lambda"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners.nondividingLambda"), H("First nondividing candidate scalar"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The first explicit candidate scalar, shared by the field cover and actual counting proof."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pascadi-modular-zero-field-mu"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners.nondividingMu"), H("Second nondividing candidate scalar"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The second explicit candidate scalar, shared by the field cover and actual counting proof."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pascadi-modular-zero-nondividing-field-cover"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners.nondividing_field_partner_cover"), H("Six ordered field-coordinate partners"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The formal cubic pencil identity and two nonzero direction determinants restrict every ordered field-coordinate partner to six explicit pairs."))), DescribeRole.Theorem)),
        edges: []));
}
