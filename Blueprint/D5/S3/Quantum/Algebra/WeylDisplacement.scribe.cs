using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class WeylDisplacementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weyl displacement words compose with a phase fixed by the symplectic pairing.",
        H("Weyl Displacement Words over a Finite Cyclic Window"),
        Blocks(
            Paragraph(Text(
                "For an arbitrary Hermitian H on Fin d x Fin e with d,e >= 2, both partial traces are unnormalized. "
                + "Write TrA = partialTraceLeft, TrB = partialTraceRight, h0 = trace(H)/(de), HA = e^(-1) TrB(H) - h0 "
                + "I_d, HB = d^(-1) TrA(H), H0 = HA tensor I_e + I_d tensor HB, and V = H - H0. Hermiticity makes h0 "
                + "real, so this is the same scalar offset as ReTr(H)/(de); only HA is centered. Partial traces and these "
                + "operations preserve Hermiticity. The trace identities give trace(HA)=0, trace(HB)=trace(H)/d, "
                + "TrA(V)=0, and TrB(V)=0.")),
            Paragraph(Text(
                "Use E = (ZMod.finEquiv d).toEquiv, W(a,b) = displacement(d,E(a),E(b)).submatrix E E, and T(a,b) = "
                + "W(a,b) tensor I_e. Here E(a).val=a.val. The shift entry is one precisely when E(i)=E(j)+1, the clock "
                + "entry on i=j is exp(2 pi i/d) raised to i.val, and T(a,b)((i,k),(j,l))=W(a,b)(i,j) times the Kronecker "
                + "delta for k=l. Thus W is exactly the positive-shift word X^a.val Z^b.val, and the window-register "
                + "unitarity gives unitarity of every T.")),
            Paragraph(Text(
                "The scalar Weyl twirl is existing mathematics: Matrix.sum_weyl_conj in LionSR/QICLean, "
                + "QICLean/Channel/WeylTwirl.lean at revision 2d1491f41311f2f2ff9b1ec0ebd47fed9172760b, with the "
                + "Apache-2.0 source attribution to Sirui Lu and TNLean contributors. Its shift convention is inverse to "
                + "the window register, giving displacement(d,a,b)=Matrix.weyl(windowRoot(d),-a,b). The bijections a -> "
                + "-E(a) and b -> E(b) preserve the d^2 summands. This is a source adaptation, not an additional "
                + "dependency on that project's Lean 4.35.0-rc3 pin.")),
            Paragraph(Text(
                "For every joint matrix Y, fix k,l and apply the scalar twirl to the arbitrary block "
                + "Y_kl(i,j)=Y((i,k),(j,l)). Entrywise tensor multiplication then gives d^(-2) sum_(a,b) T(a,b) Y "
                + "T(a,b)^adj = d^(-1) I_d tensor TrA(Y). Every joint Y is included; no simple-tensor or Hermiticity "
                + "condition is needed. TrA is unnormalized, so this formula has no factor e. Equivalently, the all-joint "
                + "tensor supplier Matrix.sum_kronecker_one_weyl_conj in QICLean/Channel/ComplementaryWeylTwirl.lean at "
                + "the same revision transports along (i,k) -> (k,E(i)). Applying the formula to this V gives a zero "
                + "average because TrA(V)=0.")),
            Paragraph(Text(
                "Define EA(Y)=e^(-1)(TrB(Y) tensor I_e). Expanding partial traces gives EA((L tensor I_e)Y(M tensor "
                + "I_e))=(L tensor I_e)EA(Y)(M tensor I_e) for arbitrary Y,L,M. Its fixed points are exactly N tensor "
                + "I_e, so EA is idempotent. The literal decomposition of H gives, for every M, [H,M tensor I_e]-EA([H,M "
                + "tensor I_e])=[V,M tensor I_e]. In particular R(a,b)=[H,T(a,b)]-EA([H,T(a,b)])=[V,T(a,b)]. Unitarity "
                + "gives R(a,b)T(a,b)^adj=V-T(a,b)V T(a,b)^adj. Averaging these d^2 terms proves the same-H "
                + "reconstruction V=d^(-2) sum_(a,b) R(a,b)T(a,b)^adj.")),
            Paragraph(Text(
                "For every square matrix A on this same index type, CStarMatrix.ofMatrixStarAlgEquiv and "
                + "StarAlgEquiv.norm_map identify the CStarMatrix norm with the Matrix.Norms.L2Operator norm; "
                + "Matrix.cstar_norm_def identifies the latter with norm(Matrix.toEuclideanCLM A). ComplexOrder supplies "
                + "the complex CStar instances. This applies to every residual as well as V, hence to their common finite "
                + "maximum delta. With c the Euclidean induced norm of H-H0, reconstruction, the triangle inequality and "
                + "unitary norm invariance give c <= delta; the commutator formula gives delta <= 2c. No coordinate proxy "
                + "or norm on a different carrier is substituted.")),
            Paragraph(Text(
                "Put hsSquare(Y)=Re(trace(Y^adj Y))/(de). Hermiticity of V, cyclicity of trace and unitarity give "
                + "trace(R(a,b)^adj R(a,b))=2 trace(V^2)-2 trace(V T(a,b) V T(a,b)^adj). The zero twirl kills the summed "
                + "cross term. Consequently (1/(2d^2)) sum_(a,b) hsSquare(R(a,b))=hsSquare(V), with both the original de "
                + "denominator and the 1/(2d^2) averaging factor.")),
            Paragraph(Text(
                "MatrixUnitCertificate.matrix_unit_eq_single and the displacement composition law express every matrix "
                + "unit in the span of the displacement family. Transport by E proves that the W(a,b) span every d by d "
                + "complex matrix. The linear residual map therefore vanishes on every M exactly when it vanishes on all "
                + "W(a,b). Together with reconstruction and the norm bounds, the following conditions are equivalent: for "
                + "every M, [H,M tensor I_e] is some N tensor I_e; for every M, EA fixes [H,M tensor I_e]; every R(a,b) "
                + "is zero; V=0; and delta=0. These statements retain arbitrary M and the actual same H throughout. They "
                + "are finite-matrix consequences of the cited results, not claims of a new Weyl twirl, a physical "
                + "realization, asymptotic bounds, thermal factorization, or dynamical and recovery estimates.")),
            Describe.Lean(
                DescribeId.Create("weyl-displacement-word"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeylDisplacement.displacement"),
                H("The displacement word"),
                StatementSource.FromAuthor(DisplacementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The displacement word at index (a, b) is the shift raised to the "
                            + "canonical natural representative of a, times the clock raised to "
                            + "the canonical natural representative of b. Both generators, their "
                            + "Weyl relation, their orders, and their unitarity are already frozen "
                            + "in the window register, which this module imports.")),
                    Paragraph(Text(
                        "The finite Weyl-Heisenberg group these words generate is classical, so "
                            + "no novelty is claimed for them. Appleby (2005), Journal of "
                            + "Mathematical Physics 46, 052107, doi 10.1063/1.1896384, defines the "
                            + "extended Clifford group as the normalizer of that group. Only the "
                            + "bibliographic identity and the published abstract were checked; the "
                            + "full text was not read, so the article is cited as background and "
                            + "not as the source of the identities proved below."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weyl-displacement-composition"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeylDisplacement.displacement_mul"),
                H("Composition law"),
                StatementSource.FromAuthor(DisplacementMulFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Two displacement words multiply to a third, scaled by a single window "
                            + "phase. The exponent of that phase is the clock index of the left "
                            + "factor times the shift index of the right factor, and nothing "
                            + "else. The proof moves a clock power across a shift power by "
                            + "iterating the frozen Weyl relation twice, once in each exponent.")),
                    Paragraph(Text(
                        "Exponents are natural representatives of residues, so the identity needs "
                            + "the generators to see their exponents only modulo the window "
                            + "cardinality. That is supplied by the frozen order relations for the "
                            + "clock and the shift and by primitivity for the phase.")),
                    Paragraph(Text(
                        "The pinned Mathlib source carries no Weyl-Heisenberg material: no file "
                            + "mentions the Weyl-Heisenberg group, the generalized Pauli group, or "
                            + "clock and shift matrices, and no file is named after Pauli or "
                            + "Heisenberg. The displacement words are nevertheless classical, so "
                            + "the cited article records that no novelty is claimed here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weyl-displacement-square"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeylDisplacement.displacement_sq"),
                H("Squaring identity"),
                StatementSource.FromAuthor(DisplacementSqFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Setting the two indices equal in the composition law gives the square of "
                            + "a displacement word as the doubled word carrying the phase whose "
                            + "exponent is the product of the two indices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weyl-displacement-two-not-commute"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeylDisplacement.displacement_two_not_commute"),
                H("The composition phase is not vacuous"),
                StatementSource.FromAuthor(DisplacementTwoFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The composition law would read the same way if every phase were one, so "
                            + "a witness is recorded that the phase does real work. On the "
                            + "two-address window the words at (0, 1) and (1, 0) do not commute. "
                            + "Assuming they did forces the window phase to be its own square, "
                            + "hence one, contradicting primitivity."))),
                DescribeRole.Theorem))));

    private static Formula Displacement(Formula window, Formula first, Formula second) =>
        Call("displacement", window, first, second);

    private static Formula WindowContext(Formula window)
    {
        return Seq(
            Forall, Sp, window, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("NeZero")), Open, window, Close,
            CloseBracket, Comma, Esc);
    }

    private static Formula Residues(Formula window, params Formula[] names)
    {
        var items = new List<Formula> { Forall, Sp };
        for (var index = 0; index < names.Length; index += 1)
        {
            items.Add(names[index]);
            if (index + 1 < names.Length)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
        }

        items.Add(Colon);
        items.Add(Sp);
        items.Add(Operatorname);
        items.Add(Grp(F.Id("ZMod")));
        items.Add(Open);
        items.Add(window);
        items.Add(Close);
        items.Add(Comma);
        items.Add(Esc);
        return Seq([.. items]);
    }

    private static Formula DisplacementFormula()
    {
        Formula m = F.Id("M");
        Formula a = F.Id("a");
        Formula b = F.Id("b");

        return Disp(Seq(
            WindowContext(m),
            Residues(m, a, b),
            Displacement(m, a, b), Sp, Eq, Sp,
            Call("shiftMatrix", m), Caret, Grp(Call("val", a)), Sp, Cdot, Sp,
            Call("clockMatrix", m), Caret, Grp(Call("val", b)), Dot));
    }

    private static Formula DisplacementMulFormula()
    {
        Formula m = F.Id("M");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula d = F.Id("d");

        return Disp(Seq(
            WindowContext(m),
            Residues(m, a, b, c, d),
            Displacement(m, a, b), Sp, Cdot, Sp, Displacement(m, c, d), Sp, Eq, Sp,
            Call("windowRoot", m), Caret, Grp(Call("val", Seq(b, Sp, Cdot, Sp, c))), Sp,
            Cdot, Sp,
            Displacement(m, Grp(a, Sp, Plus, Sp, c), Grp(b, Sp, Plus, Sp, d)), Dot));
    }

    private static Formula DisplacementSqFormula()
    {
        Formula m = F.Id("M");
        Formula a = F.Id("a");
        Formula b = F.Id("b");

        return Disp(Seq(
            WindowContext(m),
            Residues(m, a, b),
            Displacement(m, a, b), Caret, Grp(Num(2)), Sp, Eq, Sp,
            Call("windowRoot", m), Caret, Grp(Call("val", Seq(a, Sp, Cdot, Sp, b))), Sp,
            Cdot, Sp,
            Displacement(m, Grp(a, Sp, Plus, Sp, a), Grp(b, Sp, Plus, Sp, b)), Dot));
    }

    private static Formula DisplacementTwoFormula()
    {
        Formula two = Num(2);
        Formula zero = Num(0);
        Formula one = Num(1);

        return Disp(Seq(
            Displacement(two, zero, one), Sp, Cdot, Sp, Displacement(two, one, zero), Sp,
            Neq, Sp,
            Displacement(two, one, zero), Sp, Cdot, Sp, Displacement(two, zero, one), Dot));
    }
}
