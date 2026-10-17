using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma;

internal sealed class ArchimedeanJumpDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The completed-zeta Archimedean term is its mass contribution plus a nonnegative "
            + "continuous translation energy.",
        H("Archimedean Jump Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("archimedean-jump-decomposition"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition."
                        + "archimedean_jump_decomposition"),
                H("Archimedean jump decomposition"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The test function lies in the canonical carrier of even smooth compactly "
                            + "supported complex-valued functions. The displayed hArch premise is "
                            + "the exact integrability witness consumed by archimedeanTerm.")),
                    Paragraph(Text(
                        "The jump density is exp(-x/2)/(1-exp(-2x)) on positive scales, and the "
                            + "jump energy integrates the squared displacement of f by translation "
                            + "against that density. The proof derives its Levy representation from "
                            + "the frozen digamma series and applies Fourier inversion and Tonelli.")),
                    Paragraph(Text(
                        "The first public conjunct is the exact complex identity. The second "
                            + "public conjunct records positivity of the independently constructed "
                            + "continuous jump energy."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The same density has an exact interval L2 application. Let a>0, d=2*a, "
                    + "I=(-a,a], and u be complex-valued with MemLp(u,2,dx restricted to I). "
                    + "Write z=1_I*u for its zero extension and v for its d-periodic "
                    + "extension obtained from AddCircle.liftIoc at base point -a. "
                    + "For s>0, set rho(s)=exp(-s/2)/(1-exp(-2*s)), "
                    + "F0(s)=rho(s)*integral_R |z(x)-z(x-s)|^2 dx, and "
                    + "Fp(s)=rho(s)*integral_I |u(x)-v(x-s)|^2 dx. These use "
                    + "Lebesgue measure and the original half-open interval; no "
                    + "pointwise agreement of the two outer endpoints is assumed.")),
            Paragraph(Text(
                "For epsilon>=0 define K_epsilon(x,y) as the sum over every nonzero "
                    + "integer m of rho(|x-y+m*d|) when epsilon<|x-y+m*d|, with "
                    + "that summand zero otherwise. Let B_epsilon be the real part "
                    + "of integral_{I x I} conjugate(u(x))*K_epsilon(x,y)*u(y) dx dy. "
                    + "This retains both nearest images and the whole remaining "
                    + "integer lattice, with the zero image omitted.")),
            Paragraph(Text(
                "For each epsilon>0 both F0 and Fp are integrable on (epsilon,infinity), "
                    + "and their actual cutoff integrals satisfy E0_epsilon="
                    + "Ep_epsilon+B_epsilon. The half-open periodic copies are "
                    + "disjoint and exhaustive. Their zero-image cancellation, "
                    + "Fubini and the full integer sum identify the difference of "
                    + "the two correlations with the image pairing. Reflection "
                    + "gives C(-s)=conjugate(C(s)); expanding both squared "
                    + "displacements gives precisely the displayed sign and "
                    + "coefficient of B_epsilon.")),
            Paragraph(Text(
                "The boundary pairing at epsilon=0 is absolutely integrable under "
                    + "the interval L2 premise alone. For m=1 and m=-1, the possible "
                    + "corner singularities are bounded using the actual density "
                    + "and the Carleman integral estimate on the positive half-line. "
                    + "For |m|>=2, exponential decay gives a summable geometric "
                    + "majorant. Together these bounds dominate the entire image "
                    + "pairing in L1. Dominated convergence therefore gives "
                    + "B_{1/(n+1)} tending to B_0.")),
            Paragraph(Text(
                "Consequently F0 is integrable on (0,infinity) if and only if Fp "
                    + "is integrable there. On this common finite domain the full "
                    + "energies obey E0=Ep+B_0. To obtain the forward direction, "
                    + "start with the finite full zero-extension energy, subtract "
                    + "the convergent boundary sequence from its cutoff integrals, "
                    + "and apply the nonnegative AECover integrability theorem to "
                    + "Fp. Starting with the finite periodic energy and adding the "
                    + "boundary sequence proves the converse. The sets "
                    + "(1/(n+1),infinity) cover (0,infinity), so each limit identifies "
                    + "the full integral only after its integrability has been "
                    + "established. No finiteness of either full energy is included "
                    + "in the original L2 premise.")),
            Paragraph(Text(
                "This is an application of the existing density, interval transport "
                    + "and Mathlib integration results. It identifies the actual "
                    + "zero-extension and periodic energy domains and their finite "
                    + "boundary difference. A Fourier coefficient description, "
                    + "closed-form/core realization, and positivity of the full "
                    + "signed Weil form require further arguments. The displayed "
                    + "public theorem above retains its smooth even test carrier "
                    + "and exact ArchimedeanConvergent premise.")))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula test = F.Id("f");
        Formula hArch = F.Id("hArch");
        Formula convolutionSquare = Call("convolutionSquare", test);
        Formula energy = Call("archimedeanJumpEnergy", test);
        Formula constant = Seq(
            Operatorname,
            Grp(F.Id("archimedeanConstant")));
        Formula decomposition = new Formula.Relation(
            Call("archimedeanTerm", convolutionSquare, hArch),
            FormulaRelationOperator.Equal,
            new Formula.Binary(
                new Formula.Binary(
                    constant,
                    FormulaBinaryOperator.Multiply,
                    Call("l2Mass", test)),
                FormulaBinaryOperator.Add,
                energy));
        Formula nonnegative = new Formula.Relation(
            D(0),
            FormulaRelationOperator.LessThanOrEqual,
            energy);
        Formula conclusion = new Formula.Logic(
            decomposition,
            FormulaLogicOperator.And,
            nonnegative);

        return Disp(Seq(
            Forall, Sp, test, InMacro, Sp, Mathcal, Grp(F.Id("W")), Comma, Sp,
            hArch, Colon, Sp,
            Operatorname, Grp(F.Id("ArchimedeanConvergent")), Open,
            convolutionSquare, Close, Sp, Rightarrow, Sp, conclusion));
    }
}
