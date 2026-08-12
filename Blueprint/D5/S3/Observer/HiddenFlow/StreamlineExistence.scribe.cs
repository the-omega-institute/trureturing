using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HiddenFlow;

internal sealed class StreamlineExistenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical solenoid streamline data instantiate the frozen observer decomposition with a constant throat.",
        H("Existence for the Frozen Streamline Structure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-hidden-kernel-has-canonical-additive-coordinates"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/StreamlineExistence."
                        + "hiddenKernelAddEquiv"),
                H("The hidden kernel has canonical additive coordinates"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("canonicalHidden"), InMacro, Sp,
                    Operatorname, Grp(F.Id("AddEquiv")), Open,
                    F.Id("hiddenAddress"), Comma, Sp, Ker, Open, Pi, Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Chinese remaindering is additive in every modulus, and the residue-to-kernel "
                        + "map is additive coordinatewise. Upgrading the repository's two existing "
                        + "bijections and composing them gives a fixed additive identification of "
                        + "prime-adic hidden addresses with the visible kernel."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("canonical-data-instantiate-the-frozen-structure"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/StreamlineExistence."
                        + "toFrozenDecomposition"),
                H("Canonical data instantiate the frozen structure"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Forall, Sp, F.Id("t"), Comma, Esc,
                    GammaLower, Open, F.Id("t"), Close, Eq, Sp,
                    F.Id("realFlow"), Open, F.Id("r"), Open, F.Id("t"), Close, Close,
                    Plus, Sp, F.Id("k"), Close, Sp, Rightarrow, Sp,
                    F.Id("frozen"), Open, GammaLower, Comma, Sp, F.Id("r"), Comma, Sp,
                    F.Id("k"), Close, Eq, Sp,
                    Open, GammaLower, Comma, Sp, F.Id("realFlow"), Circ, Sp, F.Id("r"), Comma, Sp,
                    F.Id("canonicalHidden"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The adapter places the original path, its solenoid-valued real-flow lift, "
                        + "their visible-projection equality, and the canonical additive hidden "
                        + "coordinate equivalence into the existing frozen "
                        + "StreamlineDecomposition structure."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("the-frozen-throat-is-the-constant-hidden-offset"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/StreamlineExistence."
                        + "frozen_streamline_throat_component_constant"),
                H("The frozen throat is the constant hidden offset"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Forall, Sp, F.Id("u"), Comma, Esc,
                    GammaLower, Open, F.Id("u"), Close, Eq, Sp,
                    F.Id("realFlow"), Open, F.Id("r"), Open, F.Id("u"), Close, Close,
                    Plus, Sp, F.Id("k"), Close, Sp, Rightarrow, Sp,
                    Forall, Sp, F.Id("t"), Comma, Esc,
                    F.Id("throat"), Open, F.Id("frozen"), Open,
                    GammaLower, Comma, Sp, F.Id("r"), Comma, Sp, F.Id("k"), Close,
                    Comma, Sp, F.Id("t"), Close, Eq, Sp,
                    F.Id("canonicalHidden"), Caret, Grp(Minus, D(1)), Open, F.Id("k"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The frozen kernel difference subtracts the real-flow lift from the path. "
                        + "The reconstruction equation cancels that lift and leaves precisely "
                        + "the constant kernel element, expressed in the frozen hidden-address "
                        + "coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("every-path-instantiates-the-frozen-decomposition-uniquely"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/StreamlineExistence."
                        + "existsUnique_frozen_streamline_decomposition"),
                H("Every path instantiates the frozen decomposition uniquely"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, GammaLower, Comma, Esc,
                    Exists, Bang, Sp, F.Id("r"), Comma, Sp, F.Id("k"), Comma, Esc,
                    F.Id("r"), Open, D(0), Close, Eq, Sp,
                    F.Id("rep"), Open, GammaLower, Close, Sp, Land, Sp,
                    Forall, Sp, F.Id("t"), Comma, Esc,
                    GammaLower, Open, F.Id("t"), Close, Eq, Sp,
                    F.Id("realFlow"), Open, F.Id("r"), Open, F.Id("t"), Close, Close,
                    Plus, Sp, F.Id("k"), Sp, Land, Sp,
                    Forall, Sp, F.Id("t"), Comma, Esc,
                    F.Id("throat"), Open, F.Id("frozen"), Open,
                    GammaLower, Comma, Sp, F.Id("r"), Comma, Sp, F.Id("k"), Close,
                    Comma, Sp, F.Id("t"), Close, Eq, Sp,
                    F.Id("canonicalHidden"), Caret, Grp(Minus, D(1)), Open, F.Id("k"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The lower-stratum theorem supplies the unique normalized real lift and "
                        + "hidden kernel element. The adapter then constructs the frozen observer "
                        + "structure and proves its throat component is constant. The existing "
                        + "profinite-kernel classification is upgraded locally to an additive "
                        + "equivalence, so the public existence theorem requires no coordinate "
                        + "choice from its caller."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-constructed-frozen-throat-is-continuous"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/StreamlineExistence."
                        + "frozen_streamline_throat_component_continuous"),
                H("The constructed frozen throat is continuous"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Forall, Sp, F.Id("t"), Comma, Esc,
                    GammaLower, Open, F.Id("t"), Close, Eq, Sp,
                    F.Id("realFlow"), Open, F.Id("r"), Open, F.Id("t"), Close, Close,
                    Plus, Sp, F.Id("k"), Close, Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("Continuous")), Open,
                    F.Id("throat"), Open, F.Id("frozen"), Open,
                    GammaLower, Comma, Sp, F.Id("r"), Comma, Sp, F.Id("k"), Close,
                    Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The constant-throat identity satisfies the right-hand side of the frozen "
                        + "StreamlineTheorem equivalence on the whole real line. Applying that "
                        + "frozen theorem yields continuity, so the former conditional result is "
                        + "now a corollary after existence supplies its input structure."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Solenoid/StreamlineDecomposition")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Factorization/SolenoidProfiniteKernel")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Observer/StreamlineTheorem")),
        ]));
}
