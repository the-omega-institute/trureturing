using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class FuruichiAmlashiHyperbolicRatioDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The logarithmic mean hyperbolic ratio below parameter one.",
        H("The Furuichi–Eghbali Amlashi hyperbolic ratio"), Blocks(
            Describe.Lean(DescribeId.Create("furuichi-amlashi-hyperbolic-phi"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/FuruichiAmlashiHyperbolicRatio.phi"),
                H("The ratio"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Fourier/furuichi2022bounds")),
                Blocks(Paragraph(Text("For real r and t, phi(r,0)=1 and phi(r,t)=t (cosh t)^(1-r)/sinh t when t is nonzero. The power is the real power of the strictly positive real number cosh t."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("furuichi-amlashi-hyperbolic-claim"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/FuruichiAmlashiHyperbolicRatio.claim"),
                H("The conjectured parameter range"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Fourier/furuichi2022bounds")),
                Blocks(Paragraph(Text("For every real r below one, the complex cast of phi(r,t) fails positive definiteness: some finite real family has a matrix with entries phi(r,x(j)-x(i)) that is not positive semidefinite."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("furuichi-amlashi-hyperbolic-result"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/FuruichiAmlashiHyperbolicRatio.result"),
                H("Nonpositive definiteness below one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Fourier/furuichi2022bounds")),
                Blocks(Paragraph(Text("The full claim holds. Set a=1-r>0. The extension F(z)=exp(a Log(cosh z))/dslope(sinh,0,z) is holomorphic on the open disk of radius pi/2. In this disk the real part of cosh z is positive, so the logarithm is holomorphic, and the divided slope of sinh has no zero. On the real diameter F agrees with phi. At iy for 0<y<pi/2 it equals y (cos y)^a/sin y, which tends to zero as y increases to pi/2. Positive definiteness would force these values to be at least phi(r,0)=1, a contradiction.")),
                    Paragraph(Text("The source supplies the conjecture and the positive parameter range r at least one. This proof establishes the negative range for the stated scalar positive definite kernel. The operator-mean ordering consequence uses the external Hiai–Kosaki criterion and is not an additional formal theorem in this module."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("furuichi-eghbali-amlashi-2022-hyperbolic-ratio-not-positive-definite"),
                    ResolutionKind.Proved)))));
}
