using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class PositiveClopenMassDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Measures/PositiveClopenMass.";
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Inst(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Sp);
    private static Formula Signed(Formula K) => Call("SignedMeasure", K);
    private static Formula JordanPart(string part) =>
        Call(part, Call("toJordanDecomposition", V("s")));
    private static Formula RealMass(Formula part, Formula set) =>
        Call("real", part, set);
    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(All("K", Seq(V("Type"), Underscore, Grp(V("u")))),
            Inst("TopologicalSpace", V("K")), Inst("CompactSpace", V("K")),
            Inst("T2Space", V("K")), Inst("ZeroDimensionalSpace", V("K")),
            Inst("MeasurableSpace", V("K")), Inst("BorelSpace", V("K"))),
        Seq(All("s", Signed(V("K")))),
        Seq(Call("Regular", JordanPart("posPart")), Sp, Rightarrow),
        Seq(Call("Regular", JordanPart("negPart")), Sp, Rightarrow),
        Seq(All("V", Call("Set", V("K"))), Call("IsOpen", V("V")),
            Sp, Rightarrow),
        Seq(All("r", V("Real")),
            V("r"), Sp, Lt, Sp, RealMass(JordanPart("posPart"), V("V")),
            Sp, Rightarrow),
        Seq(Exists, Sp, V("W"), Colon, Sp, Call("Set", V("K")), Comma, Sp,
            Call("IsClopen", V("W")), Sp, Land, Sp,
            V("W"), Sp, Subseteq, Sp, V("V"), Sp, Land, Sp,
            V("r"), Sp, Lt, Sp, Call("apply", V("s"), V("W")))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Regular positive Jordan mass on an open set is realized above every strict threshold by a signed clopen subset.",
        H("Positive Jordan mass through signed clopen sets"),
        Blocks(
            Paragraph(Text(
                "K is compact Hausdorff and zero-dimensional with its Borel measurable structure. "
                + "s is the actual Mathlib real SignedMeasure on K. Both Jordan parts are finite by the Jordan decomposition and are required explicitly to be Regular. "
                + "For every open V and every real r strictly below the real positive Jordan mass of V, the conclusion supplies a clopen W contained in V with signed mass s(W) strictly above r. "
                + "No nonemptiness, metrizability, atomicity, positivity of s, or positive-half-mass premise is assumed.")),
            Describe.Lean(
                DescribeId.Create("exists-is-clopen-subset-lt-apply-of-lt-pos-part"),
                DeclarationHandle.Create(Owner + "exists_isClopen_subset_lt_apply_of_lt_posPart"),
                H("Positive clopen signed-mass bridge"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For r < 0, the empty clopen set is sufficient. For r ≥ 0, choose b with r < b < p.real(V), where p is the actual positive Jordan part. "
                        + "Mutual singularity gives a measurable N with p(N)=0 and n(Nᶜ)=0. Thus V ∩ Nᶜ retains p mass, and positive regularity gives a compact C inside it with p.real(C)>b.")),
                    Paragraph(Text(
                        "The negative part n vanishes on C. Negative regularity gives an open O containing C with n.real(O)<b-r. "
                        + "Compactness plus Hausdorffness makes C closed, and the compact zero-dimensional clopen sandwich theorem gives C ⊆ W ⊆ O ∩ V for a clopen W. "
                        + "Finite real monotonicity yields p.real(C) ≤ p.real(W) and n.real(W) ≤ n.real(O); Jordan reconstruction on W then gives s(W)>r.")),
                    Paragraph(Text(
                        "The proof composes the pinned Mathlib Jordan decomposition, regularity, real-measure monotonicity and compact zero-dimensional clopen-sandwich suppliers; the same-problem ordinary derivation supplied the proof plan. "
                        + "The explicit regularity hypotheses cover all finite and empty cases without infinite-ENNReal cancellation. "
                        + "This is a reusable positive-clopen bridge only: it does not build the CH/Talagrand recursion or prove a full problem resolution. "
                        + "For a clopen V with totalVariation(V)=totalVariation(univ)=1, finiteness gives totalVariation(Vᶜ)=0. Since total variation is the sum of the Jordan parts, the positive part vanishes on Vᶜ, so its mass on V equals its mass on the whole space. "
                        + "With the additional premise 1/2 ≤ posPart.real(univ), the bridge at r=1/3 supplies a clopen W contained in V with s(W)>1/3. Total variation normalization and support alone do not provide the positive-half-mass premise."))),
                DescribeRole.Theorem))));
}
