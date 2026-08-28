using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid;

internal sealed class StreamlineDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every continuous solenoid path has a unique base-normalized real lift and a constant hidden offset.",
        H("Canonical Streamline Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-visible-phase-representative"),
                DeclarationHandle.Create(
                    "D5/S1/Solenoid/StreamlineDecomposition.baseRepresentative"),
                H("The visible phase has a canonical representative"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("rep"), Open, GammaLower, Close, Eq, Sp,
                    Operatorname, Grp(F.Id("IcoRep")), Open,
                    Pi, Open, GammaLower, Open, D(0), Close, Close, Close,
                    InMacro, Sp, OpenBracket, D(0), Comma, Sp, D(1), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The definition chooses the unique real representative in the half-open "
                        + "interval from zero to one of the path's visible phase at the "
                        + "normalization time. This removes the integer ambiguity in a real "
                        + "lift of the additive circle."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("every-solenoid-path-has-a-unique-normalized-streamline"),
                DeclarationHandle.Create(
                    "D5/S1/Solenoid/StreamlineDecomposition."
                        + "existsUnique_normalized_streamline"),
                H("Every solenoid path has a unique normalized streamline"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, GammaLower, Colon, Sp, F.Id("C"), Open,
                    Mathbb, Grp(F.Id("R")), Comma, Sp, Mathcal, Sp, F.Id("S"), Close,
                    Comma, Sp, F.Id("t0"), Colon, Sp, Mathbb, Grp(F.Id("R")), Comma,
                    Comma, Esc, Exists, Bang, Sp, F.Id("r"), Comma, Sp, F.Id("k"), Comma, Esc,
                    F.Id("r"), Open, D(0), Close, Eq, Sp,
                    F.Id("rep"), Open, GammaLower, Close, Sp, Land, Sp,
                    F.Id("k"), InMacro, Sp, Ker, Open, Pi, Close, Sp, Land, Sp,
                    Forall, Sp, F.Id("t"), Comma, Esc,
                    GammaLower, Open, F.Id("t"), Close, Eq, Sp,
                    F.Id("realFlow"), Open, F.Id("r"), Open, F.Id("t"), Close, Close,
                    Plus, Sp, F.Id("k"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Mathlib's covering-lift theorem constructs the unique continuous real "
                            + "lift of the visible projection after fixing its value at zero. "
                            + "Subtracting the induced real flow from the original path gives a "
                            + "continuous kernel-valued motion.")),
                    Paragraph(Text(
                        "At modulus m, every point of that motion lies in the finite m-torsion "
                            + "subset of the additive circle. A continuous image of the connected "
                            + "real line inside this discrete finite set is constant. Coordinate "
                            + "extensionality gives one time-independent hidden solenoid element; "
                            + "covering-lift uniqueness and group cancellation give uniqueness of "
                            + "the complete pair.")),
                    Paragraph(Text(
                        "The pinned library was searched first. AddCircle.isCoveringMap_coe, "
                            + "IsCoveringMap.existsUnique_continuousMap_lifts, "
                            + "AddCircle.finite_torsion, Set.Finite.isDiscrete, and "
                            + "IsPreconnected.constant_of_mapsTo supply the general steps. No "
                            + "library result packages their universal-solenoid assembly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-translated-real-flow-has-a-nonzero-hidden-offset"),
                DeclarationHandle.Create(
                    "D5/S1/Solenoid/StreamlineDecomposition."
                        + "translated_realFlow_has_nonzero_hidden_offset"),
                H("A translated real flow has a nonzero hidden offset"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Bang, Sp, F.Id("r"), Comma, Sp, F.Id("k"), Comma, Esc,
                    F.Id("r"), Open, D(0), Close, Eq, Sp,
                    F.Id("rep"), Open, F.Id("translated"), Close, Sp, Land, Sp,
                    Forall, Sp, F.Id("t"), Comma, Esc,
                    F.Id("realFlow"), Open, F.Id("t"), Close, Plus, Sp,
                    F.Id("hiddenUnit"), Eq, Sp,
                    F.Id("realFlow"), Open, F.Id("r"), Open, F.Id("t"), Close, Close,
                    Plus, Sp, F.Id("k"), Sp, Land, Sp,
                    F.Id("r"), Open, D(0), Close, Neq, Sp,
                    F.Id("r"), Open, D(1), Close, Sp, Land, Sp,
                    F.Id("k"), Neq, Sp, D(0), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Translate the real-flow path by its time-one value. That value has visible "
                        + "phase zero but is nonzero at the modulus-two coordinate, where it is "
                        + "the class of one half. The unique normalized data therefore contain "
                        + "both the nonconstant identity lift and a genuinely nonzero constant "
                        + "hidden offset."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Dynamics/UniversalSolenoid")),
        ]));
}
