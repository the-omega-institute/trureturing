using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Scale;

internal sealed class MinkowskiModelSetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two real embeddings form a golden lattice whose internal window selects model-set points.",
        H("Golden Minkowski Model Set"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("minkowski-lattice-window-and-labeled-model-set"),
                DeclarationHandle.Create("D5/S1/Scale/MinkowskiModelSet.minkowski_model_set_spec"),
                H("Minkowski lattice, window, and labeled model set"),
                    StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                                    LibraryNoteRef.Create("D5/L/baakefrankgrimm2021three")),
                Blocks(Paragraph(Text(
                                    "The physical and conjugate embeddings give an injective diagonal range. An internal-space window selects physical projections, and the labeled extension pairs selected points with their joint golden coordinates."))),
                DescribeRole.Definition
            ),
            Describe.Remark(
                DescribeId.Create("value-and-code-geometries"),
                DeclarationHandle.Create("D5/S1/Scale/MinkowskiModelSet.minkowski_model_set_spec"),
                H("Value and code geometries"),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/baakefrankgrimm2021three")),
                Blocks(Paragraph(Text(
                    "The same carrier admits a lattice-like value reading and a cut-and-project code reading. The internal window justifies calling the code geometry a model set; it does not by itself provide a Bloch decomposition, a spectral gap theorem, or a periodic classifier for the code layer.")))),
            DocumentBlock.Describe.Remark(
                DescribeId.Create("off-diagonal-load-and-diagonal-blindness"),
                H("Off-diagonal load and diagonal blindness"),
                DescribeStatement.FromFormula(NotEqual(Id("Zqc"), Id("zeta"))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The source assigns the two-sided code genuine load only away from the diagonal: its cited off-diagonal results are reported to fail under replacement encodings. The classical zeta diagonal is instead code-blind whenever it is reached only through diagonal decomposition. Whether an off-diagonal invariant can return analytic information to that diagonal remains explicitly open as O-5.")))
            ),
            DocumentBlock.Describe.Remark(
                DescribeId.Create("scaled-zero-images-need-an-independent-engine"),
                H("Scaled zero images need an independent engine"),
                DescribeStatement.FromFormula(new Formula.Fraction(
                    Id("rho"),
                    Add(
                        Multiply(Id("a"), new Formula.Power(new Formula.Phi(), Num(2))),
                        Multiply(Id("b"), new Formula.Power(new Formula.Phi(), Num(3)))))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "In the source cascade, every zeta zero rho produces the image lattice rho/(a*phi^2 + b*phi^3) whenever the corresponding exponent is nonzero. The leading scale ratio is phi, and the band endpoints interlace pole and critical images, with 1/(2*phi^3) as the stated left endpoint. This self-similar overlay is only a rearrangement of identities built from zeta, so without new input it gives no compressed zero argument. Its positive use is conditional: genuinely independent control of one quasiperiodic band, for example trace-map hyperbolicity, would constrain an entire family of phi-scaled zeta segments. The recursive skeleton is present; the independent engine is still O-5.")))
            ),
            DocumentBlock.Describe.Remark(
                DescribeId.Create("the-continuation-wall-is-a-transported-boundary"),
                H("The continuation wall is a transported boundary"),
                DescribeStatement.FromFormula(NotEqual(Id("continuationWall"), Id("zeroLine"))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The cyclotomic Estermann-Kurokawa mechanism relies on explicit control of polynomial-factor zeros. For irrational exponents the source replaces that input by two obligations: scaled independence of zeta zeros on the zero side and Hecke-Mahler zero avoidance on the axis side. Excluding those two failure channels unconditionally is the outstanding N-4 subaccount of O-5. The source then separates three geometries: the proved code spectrum on a circle, the conjectural zeta-zero spectrum on a line, and a conditional continuation wall on an axis whose bricks are transported critical zeros. The no-door reading of that wall is another projection of scaled zero independence. This dictionary rearranges zeta information and supplies no independent zero input; its new content is the claimed boundary of Zqc as an analytic object. A second independent derivation of the full exponent table is also recorded as passing without a new audit exception.")))
            )),
[
                        DocumentEdge.Dependency.Create(
                            GidRef.Create("D5/S1/Depth/JointCoordinates")),
                    ]));
}
