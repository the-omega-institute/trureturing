using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline.Cayley;

internal sealed class PositiveExactRealizationFiberDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Midline/Cayley/PositiveExactRealizationFiber."
            + "positive_exact_realization_fiber_nonempty_implies_rh";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive exact Cayley realization with nonzero exhaustive zero modes forces the "
            + "Riemann hypothesis, and RH supplies the canonical realization.",
        H("Positive Exact Realization Fiber"),
        Blocks(Describe.Lean(
            DescribeId.Create("positive-exact-realization-fiber-implies-rh"),
            DeclarationHandle.Create(Declaration),
            H("A nonempty positive exact realization fiber forces RH"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For ZeroData Z, a positive exact realization consists of a bounded "
                        + "operator C and a nonzero vector psi_v for every multiplicity "
                        + "coordinate v. Exactness is the eigenmode identity C psi_v = "
                        + "c_v psi_v, where c_v = (rho_v - 1) / rho_v; positivity is the "
                        + "Gram identity C* C = I.")),
                Paragraph(Text(
                    "The source proof silently needs every psi_v to be nonzero and its zero "
                        + "family to exhaust all nontrivial zeta zeros. The formal statement "
                        + "makes both requirements explicit. The exhaustiveness binder uses "
                        + "the same public bridge as ZeroHilbertCayleyUnitarity.")),
                Paragraph(Text(
                    "The Gram identity makes C an isometry. Applying norm preservation to a "
                        + "nonzero eigenmode forces |c_v| = 1, and the imported zero-Hilbert "
                        + "Cayley equivalence yields RH. No critical-line algebra is reproved.")),
                Paragraph(Text(
                    "The companion declaration canonicalPositiveExactRealization constructs "
                        + "C from the diagonal zeroCayleyOperator and psi_v from the canonical "
                        + "single-coordinate vector under RH. Thus the file also proves that "
                        + "the realization fiber is nonempty exactly when RH holds."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Midline/Cayley/ZeroHilbertCayleyUnitarity")),
        ]));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula EqualTo(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[0];
        for (var index = 1; index < clauses.Length; index++)
        {
            result = Seq(Grp(result), Sp, Land, Sp, Grp(clauses[index]));
        }

        return result;
    }

    private static Formula Implies(Formula premise, Formula conclusion) =>
        Seq(Grp(premise), Sp, Rightarrow, Sp, Grp(conclusion));

    private static Formula TheoremFormula()
    {
        Formula z = F.Id("Z");
        Formula rho = Rho;
        Formula n = F.Id("n");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula zeroAtN = Call("zero", z, n);
        Formula trivialZero = Seq(Minus, D(2), Grp(n, Plus, D(1)));
        Formula nontrivial = Seq(
            Neg, Sp, Exists, Sp, n, Sp, InMacro, Sp, natural, Comma, Sp,
            EqualTo(rho, trivialZero));
        Formula exhaustive = Seq(
            Forall, Sp, rho, Sp, InMacro, Sp, complex, Comma, Sp,
            Implies(
                And(
                    EqualTo(Call("riemannZeta", rho), D(0)),
                    nontrivial,
                    Seq(rho, Sp, Neq, Sp, D(1))),
                Seq(Exists, Sp, n, Sp, InMacro, Sp, natural, Comma, Sp,
                    EqualTo(zeroAtN, rho))));
        Formula fiber = Call("PositiveExactRealization", z);
        Formula conclusion = Implies(
            Call("Nonempty", fiber),
            Seq(Operatorname, Grp(F.Id("RiemannHypothesis"))));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, z, Colon, Sp, Operatorname, Grp(F.Id("ZeroData")), Comma),
            Seq(Grp(exhaustive), Sp, Rightarrow, Sp, conclusion, Dot),
        ]));
    }
}
