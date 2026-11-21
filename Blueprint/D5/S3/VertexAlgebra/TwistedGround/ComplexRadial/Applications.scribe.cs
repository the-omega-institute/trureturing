using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial;

internal sealed class ApplicationsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex radial identities for all signs of the original J and T kernels",
        H("Applications of the literal kernel identity"),
        Blocks(
            Paragraph(Text("In each identity u, v and z are complex and satisfy "
                + "‖u‖ + ‖z‖ < 1 and ‖v‖ + ‖z‖ < 1. The sign labels e and f are Booleans, "
                + "with true denoting the positive label. The candidates on the right are the signed "
                + "formulas of OriginalGaussianExternalSignedCandidate.")),
            Describe.Lean(DescribeId.Create("complex-radial-positive-j-equality"),
                DeclarationHandle.Create(Prefix + "positiveJ_eq_candidateJ_complex"),
                H("Positive J equality"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On this domain, kernelMode(false,true,true,u,v,z) = "
                    + "candidateJ(true,true,u,v,z²). The two-positive signed formula is the positive "
                    + "J formula. "),
                    Ref("D5/S3/VertexAlgebra/TwistedGround/PositiveJ/Identification.positiveJ_eq_candidateJ"),
                    Text(" supplies the real equality for kernelMode_eq_candidate_complex_of_real."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complex-radial-negative-label-j-equality"),
                DeclarationHandle.Create(Prefix + "signedJ_eq_candidateJ_complex"),
                H("J equality with a negative label"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On this domain, if e = false or f = false, "
                    + "kernelMode(false,e,f,u,v,z) = candidateJ(e,f,u,v,z²). "
                    + "The transport theorem takes its real equality from "
                    + "OriginalGaussianSignedIdentification.six_sector_identification with square = false."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complex-radial-all-signs-j-equality"),
                DeclarationHandle.Create(Prefix + "allSignsJ_eq_candidateJ_complex"),
                H("J equality for every sign pair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary e and f on this domain, "
                    + "kernelMode(false,e,f,u,v,z) = candidateJ(e,f,u,v,z²). "
                    + "The three pairs with a false label use signedJ_eq_candidateJ_complex. "
                    + "The pair (true,true) uses positiveJ_eq_candidateJ_complex."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complex-radial-negative-label-t-equality"),
                DeclarationHandle.Create(Prefix + "signedT_eq_candidateT_complex"),
                H("T equality with a negative label"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On this domain, if e = false or f = false, "
                    + "kernelMode(true,e,f,u,v,z) = candidateT(e,f,u,v,z²). "
                    + "The transport theorem takes its real equality from "
                    + "OriginalGaussianSignedIdentification.six_sector_identification with square = true."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complex-radial-positive-t-equality"),
                DeclarationHandle.Create(Prefix + "positiveT_eq_candidateT_complex"),
                H("Positive T equality"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On this domain, kernelMode(true,true,true,u,v,z) = "
                    + "candidateT(true,true,u,v,z²). The two-positive signed T formula agrees with "
                    + "the positive rational candidate by the equality of their denominators and "
                    + "numerators. PositiveT.GeneratorIdentification.positiveT_eq_candidateT then "
                    + "supplies the real equality for kernelMode_eq_candidate_complex_of_real."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complex-radial-all-signs-t-equality"),
                DeclarationHandle.Create(Prefix + "allSignsT_eq_candidateT_complex"),
                H("T equality for every sign pair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary e and f on this domain, "
                    + "kernelMode(true,e,f,u,v,z) = candidateT(e,f,u,v,z²). "
                    + "The three pairs with a false label use signedT_eq_candidateT_complex. "
                    + "The pair (true,true) uses positiveT_eq_candidateT_complex."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complex-radial-all-signs-jt-equality"),
                DeclarationHandle.Create(Prefix + "allSignsJT_eq_candidates_complex"),
                H("Joint J and T identities"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the same arbitrary pair e and f on this domain, "
                    + "kernelMode(false,e,f,u,v,z) = candidateJ(e,f,u,v,z²) and "
                    + "kernelMode(true,e,f,u,v,z) = candidateT(e,f,u,v,z²). "
                    + "The conjunction uses allSignsJ_eq_candidateJ_complex and "
                    + "allSignsT_eq_candidateT_complex directly."))),
                DescribeRole.Theorem))));
}
