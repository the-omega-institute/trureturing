using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Scale;

internal sealed class FibonacciEigenDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("The Fibonacci substitution has two golden eigenpairs and an exact contracting error.",
H("Fibonacci Substitution Spectrum"),
Blocks(
            Describe.Lean(
                DescribeId.Create("golden-eigenpairs-and-contracting-error"),
                DeclarationHandle.Create("D5/S1/Scale/FibonacciEigen.fibonacci_substitution_spec"),
                H("Golden eigenpairs and contracting error"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc, Operatorname, Grp(F.Id("expandingEigenvector")), Neq, Sp, D(0), Sp, Land, Sp, Operatorname, Grp(F.Id("fibonacciSubstitution")), Operatorname, Grp(F.Id("expandingEigenvector")), Eq, Varphi, Operatorname, Grp(F.Id("expandingEigenvector")), Sp, Land, Sp, Operatorname, Grp(F.Id("contractingEigenvector")), Neq, Sp, D(0), Sp, Land, Sp, Operatorname, Grp(F.Id("fibonacciSubstitution")), Operatorname, Grp(F.Id("contractingEigenvector")), Eq, Operatorname, Grp(F.Id("contractingEigenvalue")), Operatorname, Grp(F.Id("contractingEigenvector")), Sp, Land, Sp, Open, F.Id("F"), Underscore, Grp(F.Id("n")), Varphi, Minus, F.Id("F"), Underscore, Grp(F.Id("n"), Plus, D(1)), Close, Eq, Minus, Operatorname, Grp(F.Id("contractingEigenvalue")), Caret, Grp(F.Id("n"))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/koshy2001fibonacci")),
                Blocks(Paragraph(Text(
                    "The explicit substitution matrix has nonzero expanding and contracting eigenvectors, and the same theorem gives the exact signed Fibonacci error for every natural index.")),
                    Paragraph(
                        Text("Residue-period applications of the same substitution: "),
                        Ref(LibraryNoteRef.Create("D5/L/renault2013periodrankorder").Value),
                        Text(". PCL in the existing WSS dossier separates sampling stride, "
                            + "external prime-period coupling and native factor multiplicities. "
                            + "It gives exact joint-period thresholds, arbitrary-depth auxiliary "
                            + "period carriers, and the paired ternary block periods. "
                            + "Those are ordinary mathematical results with their own rank "
                            + "and lifting proofs, not conclusions of this real-eigenpair "
                            + "Lean theorem. The formal statement and provenance above "
                            + "remain unchanged; no WSS prime is constructed by this link.")),
                    Paragraph(
                        Text("Cubic reciprocity on the same integer block depths: "),
                        Ref(LibraryNoteRef.Create("D5/L/dunn2024cubicreciprocity").Value),
                        Text(". GCR in the existing WSS dossier proves single-layer and "
                            + "interlevel cubic-character balances, individual earlier-prime "
                            + "conditions and a Kummer interpretation. Under a P-squared "
                            + "Q-cubed block factorization it constrains the square factor. "
                            + "These are ordinary proofs using classical reciprocity, "
                            + "not conclusions of this Lean declaration. No WSS example, "
                            + "elimination of that pattern or kernel certification is claimed.")),
                    Paragraph(
                        Text("The continuation GCR.7-GCR.12 retains both conjugate prime "
                            + "directions, the inert-prime-two balance and the resulting "
                            + "normal Kummer extension. It derives rational cubic conditions "
                            + "on the square factor, proves their comparison-prime compatibility "
                            + "and gives an exact irreducible cubic Thue descent with its "
                            + "original Lucas-coordinate condition. Source roles remain in "),
                        Ref(LibraryNoteRef.Create("D5/L/dunn2024cubicreciprocity").Value),
                        Text(". These are ordinary mathematical statements; the Lean "
                            + "declaration, authored formula and provenance above are unchanged.")),
                    Paragraph(
                        Text("GIR in that same companion Library note constructs actual "
                            + "independent points on two fixed elliptic curves from the "
                            + "golden blocks, with exact common-field degrees, discriminants "
                            + "and an orthogonal generated height lattice. It also constructs "
                            + "a cubic order whose maximal-order index has exactly the "
                            + "original WSS prime support in each block. These ordinary "
                            + "proofs use separately credited classical inputs; no rank "
                            + "oracle, WSS existence result or additional Lean conclusion "
                            + "is asserted by this context link.")),
                    Paragraph(
                        Text("GNT in the same companion computes the exact local "
                            + "normalization modules, conductor and intrinsic point-blowup "
                            + "chain of that order. Its arithmetic differential module "
                            + "is identified with the earlier Fibonacci mapping-torus "
                            + "torsion, and its marked three-torus cover has explicit "
                            + "cone homology. Complex torus links are separate comparison "
                            + "models, not mixed-characteristic analytic identifications. "
                            + "These are ordinary proofs; no new WSS prime or additional "
                            + "Lean conclusion is asserted."))),
                DescribeRole.Theorem)),
[
                        DocumentEdge.Dependency.Create(
                            GidRef.Create("D5/S0/Carrier/GoldenRatio")),
                    ]));
}
