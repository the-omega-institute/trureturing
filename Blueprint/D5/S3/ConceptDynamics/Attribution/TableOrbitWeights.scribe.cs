using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class TableOrbitWeightsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Attribution/TableOrbitWeights.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orbit mass variables for invariant probability tables and their event constraints.",
        H("The orbit program for finite equivariant probability kernels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("invariant-event-masses-iff"),
                DeclarationHandle.Create(Prefix + "invariant_event_masses_iff"),
                H("Invariant event masses are exactly the linear combinations of orbit frequencies"),
                StatementSource.FromAuthor(EventEquivalence()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A group G acts on a finite type T. Events A are finite subsets of T "
                        + "indexed by an arbitrary type I, and m gives their prescribed real masses. "
                        + "An invariant law on T has nonnegative weights summing to one and is constant "
                        + "on every orbit. The orbit frequency of an event counts its intersection with "
                        + "the orbit and divides by the orbit size.")),
                    Paragraph(Text("An invariant law with the prescribed event masses gives orbit totals "
                        + "that are nonnegative and sum to one. Conversely, distribute each orbit total "
                        + "uniformly within its orbit. Every prescribed event is then recovered by the "
                        + "same linear combination of its orbit frequencies."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("maximal-invariant-event-mass"),
                DeclarationHandle.Create(Prefix + "maximal_invariant_event_mass"),
                H("The orbit program attains the maximum invariant mass of the target event"),
                StatementSource.FromAuthor(EventMaximum()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix an additional target event B in a finite G-set. Assume that some "
                        + "invariant probability law has all the prescribed event masses. The feasible "
                        + "orbit totals form a nonempty closed subset of a compact box. The target "
                        + "mass is a linear objective and has a maximizer there.")),
                    Paragraph(Text("For every real value a, an invariant law satisfying the event "
                        + "constraints and assigning a to B exists exactly when a feasible orbit vector "
                        + "has objective value a."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("maximal-table-fixed-mass"),
                DeclarationHandle.Create(Prefix + "maximal_table_fixed_mass"),
                H("An arbitrary subgroup's fixed seed mass is the attained orbit program optimum"),
                StatementSource.FromAuthor(KernelMaximum()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A group G acts on a nonempty finite input type X in universe v "
                        + "and a finite output type Y in universe w with decidable equality. "
                        + "The deterministic table type has a finite enumeration. "
                        + "Let H be a subgroup of G and let P be a G-covariant probability kernel. "
                        + "The table action simultaneously transports arguments and outputs. "
                        + "The linear constraints prescribe all evaluation marginals, and the target "
                        + "event consists of the tables fixed by H.")),
                    Paragraph(Text("The chosen vector of orbit totals is feasible and maximizes the "
                        + "target objective over every feasible vector. That value bounds the H-fixed "
                        + "mass of every finite seed type in arbitrary universe s with nonnegative, "
                        + "normalized, G-invariant weights and a G-covariant deterministic readout "
                        + "having marginals P. A finite seed type in the maximum of v and w attains "
                        + "the value with strictly positive normalized G-invariant weights and a "
                        + "G-covariant deterministic readout with marginals P.")),
                    Paragraph(Text("Pushing a calibration to its deterministic tables preserves the "
                        + "marginals and can increase the fixed mass. The optimizer lifts back by "
                        + "restricting its table law to the positive support and taking evaluation "
                        + "as the deterministic readout."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula EventEquivalence()
    {
        Formula g = F.Id("G");
        Formula t = F.Id("T");
        Formula a = F.Id("A");
        Formula m = F.Id("m");
        Formula p = F.Id("p");
        Formula z = F.Id("z");
        return Disp(Seq(Forall, Sp, g, Comma, Sp, t, Comma, Sp, a, Comma, Sp, m,
            Comma, Sp, Open, Exists, Sp, p, Comma, Sp, Call("InvariantLaw", g, t, a, m, p), Close,
            Sp, Iff, Sp, Open, Exists, Sp, z, Comma, Sp, Call("FeasibleOrbitMasses", g, t, a, m, z), Close));
    }

    private static Formula EventMaximum()
    {
        Formula a = F.Id("A");
        Formula m = F.Id("m");
        Formula b = F.Id("B");
        Formula z = F.Id("z");
        return Disp(Seq(Call("InvariantEventConstraintsFeasible", a, m), Sp, Rightarrow,
            Sp, Exists, Sp, z, Comma, Sp, Call("OptimalOrbitMasses", a, m, b, z),
            Sp, Land, Sp, Call("SameAttainableTargetMasses", a, m, b)));
    }

    private static Formula KernelMaximum()
    {
        Formula g = F.Id("G");
        Formula h = F.Id("H");
        Formula x = F.Id("X");
        Formula y = F.Id("Y");
        Formula p = F.Id("P");
        Formula v = F.Id("v");
        Formula w = F.Id("w");
        Formula s = F.Id("s");
        Formula z = F.Id("z");
        return Disp(Seq(Call("Subgroup", h, g), Sp, Land, Sp, Call("NonemptyFiniteInput", x, v),
            Sp, Land, Sp, Call("FiniteOutputWithDecidableEquality", y, w),
            Sp, Land, Sp, Call("FiniteTableType", x, y),
            Sp, Land, Sp, Call("CovariantProbabilityKernel", g, x, y, p),
            Sp, Rightarrow, Sp, Exists, Sp, z, Comma, Sp, Call("OptimalKernelOrbitMasses", h, p, z),
            Sp, Land, Sp, Call("UniversalCalibrationBound", h, p, z, s),
            Sp, Land, Sp, Call("PositiveCalibrationAttainment", h, p, z, Call("MaxUniverse", v, w))));
    }
}
