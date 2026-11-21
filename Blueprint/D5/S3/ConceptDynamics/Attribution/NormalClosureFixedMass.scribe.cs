using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class NormalClosureFixedMassDocument : IScribeDocumentDefinition
{
    private const string Theorem = "D5/S3/ConceptDynamics/Attribution/NormalClosureFixedMass."
        + "full_subgroup_fixed_seed_mass_iff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A criterion for full subgroup-fixed mass in finite equivariant calibrations.",
        H("The normal closure determines full fixed mass"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("full-subgroup-fixed-seed-mass-iff"),
                DeclarationHandle.Create(Theorem),
                H("Full subgroup-fixed seed mass is equivalent to row support for the normal closure"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A group G acts on a finite input type X in universe v and on a finite "
                        + "output type Y in universe w with decidable equality. A probability kernel P "
                        + "has nonnegative entries, normalized rows and is covariant under G. Let H "
                        + "be a subgroup of G and let N be the normal closure of H in G.")),
                    Paragraph(Text(
                        "The seed type belongs to the maximum of the input and output universes. PositiveCalibration "
                        + "requires a G-action on that type, strictly positive normalized G-invariant weights, and a "
                        + "pointwise G-covariant deterministic readout realizing each entry of P as the total "
                        + "weight of seeds with the indicated output. FixedMass is the total weight "
                        + "of seeds fixed by every element of the subgroup.")),
                    Paragraph(Text(
                        "When the H-fixed event has full weight, positivity forces each seed to be fixed "
                        + "by H. The kernel of the seed action is normal and contains H, so it contains "
                        + "N as well. Covariance then forces the stated row support. For an empty input type one seed of weight one with trivial group action suffices. For nonempty input the row "
                        + "support gives mass one in every row for the N stabilizer criterion. The "
                        + "normal-subgroup maximum supplies a calibration with full N-fixed mass, "
                        + "which also has full H-fixed mass."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Statement()
    {
        Formula g = F.Id("G");
        Formula h = F.Id("H");
        Formula p = F.Id("P");
        Formula x = F.Id("X");
        Formula y = F.Id("Y");
        Formula v = F.Id("v");
        Formula w = F.Id("w");
        Formula a = F.Id("a");
        Formula f = F.Id("f");
        Formula seed = F.Id("S");
        Formula n = Call("NormalClosure", h);
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula kernel = Seq(x, Sp, Times, Sp, y, Sp, To, Sp, reals);
        Formula point = F.Id("x");
        Formula value = F.Id("y");
        Formula element = F.Id("n");
        return Disp(Seq(Forall, Sp, g, Comma, Sp, x, Comma, Sp, y, Comma, Sp,
            h, Colon, Call("Subgroup", g), Comma, Sp, p, Colon, kernel, Comma, Sp,
            Call("CovariantProbabilityKernel", p), Sp, Rightarrow, Sp,
            Open, Open, Exists, Sp, seed, Colon, Call("FiniteSeedType", Call("MaxUniverse", v, w)),
            Comma, Sp, a, Colon, seed, Sp, To, Sp, reals, Comma, Sp,
            f, Colon, x, Sp, Times, Sp, seed, Sp, To, Sp, y, Comma, Sp,
            Call("PositiveCalibration", g, p, seed, a, f), Sp, Land, Sp, Call("FixedMass", h, a),
            Eq, D(1), Close, Sp, Iff, Sp,
            Open, Forall, Sp, point, Colon, x, Comma, Sp, value, Colon, y, Comma, Sp,
            D(0), Lt, Call("P", point, value), Sp, Rightarrow, Sp, Forall, Sp, element, Colon, n,
            Comma, Sp, element, Sp, Cdot, Sp, point, Eq, point, Sp, Rightarrow, Sp,
            element, Sp, Cdot, Sp, value, Eq, value, Close, Close));
    }
}
