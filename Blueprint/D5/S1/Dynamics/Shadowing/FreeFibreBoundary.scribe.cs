using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class FreeFibreBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Dynamics/Shadowing/FreeFibreBoundary.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Dynamics/peng2026shadowing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A generic binary-shift source refutes the unrestricted compact Hausdorff zero-dimensional shadowing-cover assertion.",
        H("Peng Question 5.1: the free-fibre obstruction"),
        Blocks(
            Node("finite-initial-language", "Finite initial graph presentation", "finite_initial_presentation_to_graphLanguage",
                "Every set of binary names presented by a finite directed graph, a vertex label, and an arbitrary initial vertex set is exactly a finite graph language with Boolean coded edge, label, and initial data.", DescribeRole.Theorem),
            Node("marked-observation", "Marked clopen image language", "semiconj_clopen_image_is_finiteGraphLanguage",
                "If T shadows and phi is a continuous shift semiconjugacy into binary names, then the image phi(W) of every clopen W is exactly a finite initial graph language. The initial graph vertices are restricted by the marker at time zero, so the statement covers all natural times including zero and does not assume T is onto.", DescribeRole.Theorem),
            Node("section-clopen", "Convergent section restriction", "finiteGraphLanguage_section_isClopen",
                "For the first-disagreement convergent section S0 consisting of the generic name and one selected name in each finite fibre, the restriction of every finite graph language is clopen in S0 whenever the generic name locally decides that language.", DescribeRole.Theorem),
            Node("source-shadowing", "Free-fibre source shadowing", "freeFibreSource_hasShadowing",
                "Given a compact Hausdorff continuous open onto map p:T to the one-point compactification of the naturals and a generic binary name a, the disjoint source consisting of the pullback of p along firstDifference a and a binary shift copy has a continuous forward map with finite-open-cover shadowing. The proof fixes finite control before the pseudo-orbit and pays the time-zero lift explicitly.", DescribeRole.Theorem),
            Node("cover-resolution", "A hypothetical cover forces an open resolution", "freeFibre_cover_forces_resolution",
                "For every compact Hausdorff zero-dimensional shadowing system (Y,tau), every continuous onto q from Y to the free-fibre source, and every equivariant semiconjugacy, the restriction over the convergent section yields a continuous onto map r to T whose composite p composed r is open on the whole one-point base. No shadowing or invariance is assumed of the restriction Y0; no injectivity, global openness, or fibre restriction is imposed on the upstairs cover.", DescribeRole.Theorem),
            Node("claim", "Peng's unrestricted Question 5.1", "claim",
                "For every compact Hausdorff space X with a continuous forward map f and finite-open-cover shadowing, there should exist a compact Hausdorff zero-dimensional space Y with a continuous forward map tau and shadowing, together with a continuous onto q:Y to X satisfying q composed tau equals f composed q. The statement retains arbitrary fibres, transients, dynamics, and natural time zero.", DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Question 5.1 is refuted"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Use the supplied compact Hausdorff continuous open surjection p:T to the one-point compactification of the naturals with no compact Hausdorff zero-dimensional open resolution. Choose the locally deciding generic binary name, form the first-disagreement pullback, and append the binary full shift as the core. The source is compact Hausdorff and shadows. Any cover permitted by claim produces, by the marked finite-language lemma and the clopen convergent section, an open zero-dimensional resolution of p, contradicting the supplied static witness. The construction has no metrizability, countability, onto-dynamics, invertibility, prescribed fibre, core, or transient restriction. The result establishes kernel status and repository attribution only; it makes no priority, uniqueness, publication, or official-acceptance claim."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("peng-2026-zero-dimensional-shadowing-extension"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), role);
}
