using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class CubicThetaLatticeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/CubicThetaLattice.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/huang2025signpatterns");
    private static readonly LibraryNoteRef Original =
        LibraryNoteRef.Create("D5/L/Fourier/bringmann2024periodic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Eisenstein norm fibres give a complete cubic lattice dissection.",
        H("Cubic Theta Lattice Dissection"),
        Blocks(
            Paragraph(Text("The norm is Q(x,y)=x^2+xy+y^2 and the shifted exponent is e(x,y)=3Q(x,y)-2x-y. Every lattice point is included. The two theta series count complete finite fibres over the integers, and their monomial sums converge coefficientwise. These lattice series are not defined by Euler products.")),
            Node("norm", "Eisenstein norm", "eisensteinNorm", "The integer binary norm Q on all ordered integer pairs.", DescribeRole.Definition),
            Node("core-exponent", "Three-core lattice exponent", "coreExponent", "The integral shifted exponent 3Q(x,y)-2x-y in the source's three-core sum.", DescribeRole.Definition),
            Node("norm-fiber", "Norm fibres", "NormFiber", "The complete integer-pair fibre of norm n, for each natural n.", DescribeRole.Definition),
            Node("core-fiber", "Shifted fibres", "CoreFiber", "The complete integer-pair fibre of shifted exponent n.", DescribeRole.Definition),
            Node("coercive", "Coercivity", "norm_coercive", "The exact identity 2Q=x^2+y^2+(x+y)^2 bounds both coordinates.", DescribeRole.Theorem),
            Node("nonnegative", "Nonnegative norm", "norm_nonneg", "The norm is nonnegative at every integer pair.", DescribeRole.Theorem),
            Node("shift", "Integral shifted norm", "core_shift_norm", "Q(3x-1,3y)=3e(x,y)+1. This retains the linear terms -2x-y exactly.", DescribeRole.Theorem),
            Node("exponent-nonnegative", "Nonnegative shifted exponent", "core_exponent_nonneg", "Integrality and the shifted norm identity imply e(x,y) is nonnegative.", DescribeRole.Theorem),
            Node("norm-finite", "Finite norm fibres", "normFiber_finite", "Coercivity puts each norm fibre in an explicit finite integer rectangle.", DescribeRole.Definition),
            Node("core-finite", "Finite shifted fibres", "coreFiber_finite", "The injective shift (x,y) to (3x-1,3y) embeds each shifted fibre into a finite norm fibre.", DescribeRole.Definition),
            Node("norm-series", "Norm theta series", "normTheta", "Coefficient n is the rational image of the cardinality of the complete norm fibre.", DescribeRole.Definition),
            Node("core-series", "Shifted theta series", "coreTheta", "Coefficient n is the rational image of the cardinality of the complete shifted fibre. No product identity is assumed.", DescribeRole.Definition),
            Node("core-zero", "Zero shifted fibre", "core_fiber_zero", "The unique integer pair of shifted exponent zero is (0,0).", DescribeRole.Theorem),
            Node("positive-normalization", "Coefficient positivity and normalization", "theta_nonnegative_and_normalized", "Both lattice series have nonnegative coefficients and constant coefficient one.", DescribeRole.Theorem),
            Node("counted-fibres", "Finite-fibre series", "hasSum_counted_fibers", "For every nonnegative integer weight on the integer-pair lattice with finite fibres, the fibre-cardinality series is the full coefficientwise monomial sum.", DescribeRole.Theorem),
            Node("lattice-sums", "The full lattice sums", "hasSum_lattice_theta", "For every topology on the rational coefficient field, both fibre series are the coefficientwise sums of all lattice monomials at their nonnegative integral exponents.", DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cubic-theta-lattice-norm-tripling"),
                DeclarationHandle.Create("D5/S3/Arith/ModularForms/CubicThetaLattice.normTripling"),
                H("Norm-tripling map"), StatementSource.FromAuthor(NormTriplingFormula()),
                AssessedProvenance.FromRepo(Source, Original),
                Blocks(Paragraph(Text("The integer map sends (x,y) to (x-y,x+2y)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cubic-theta-lattice-norm-third"),
                DeclarationHandle.Create("D5/S3/Arith/ModularForms/CubicThetaLattice.normThird"),
                H("Integer inverse-coordinate map"), StatementSource.FromAuthor(NormThirdFormula()),
                AssessedProvenance.FromRepo(Source, Original),
                Blocks(Paragraph(Text("The integer coordinate map sends (u,v) to ((2u+v)/3,(v-u)/3), with integer division in both coordinates."))),
                DescribeRole.Definition),
            Node("triple-equiv", "Norm-tripling equivalence", "normTripleEquiv", "The map (x,y) to (x-y,x+2y) identifies norm-n and norm-3n fibres. The inverse uses the exact integer divisions (2u+v)/3 and (v-u)/3.", DescribeRole.Definition),
            Node("core-equiv", "Six rotated core fibres", "normCoreEquiv", "All norm-(3n+1) points are uniquely obtained by one of six rotations of (3x-1,3y), with e(x,y)=n. Coordinate residues make the six images disjoint and exhaustive.", DescribeRole.Definition),
            Node("residue-counts", "All-index residue counts", "norm_fiber_residue_counts", "The norm-fibre counts at 3n, 3n+1 and 3n+2 are respectively the norm-n count, six times the shifted-n count, and zero. The variable n is unrestricted.", DescribeRole.Theorem),
            Node("dissection", "Cubic lattice dissection", "norm_theta_dissection", "The complete formal power-series identity A(X)=A(X^3)+6X T_lattice(X^3) follows from the fibre equivalences and exact PowerSeries.expand coefficients. It includes degree zero.", DescribeRole.Theorem),
            Node("extra-0", "Norm residues", "norm_mod_three", "The Eisenstein norm has only residues zero and one modulo three, detected by the coordinate difference.", DescribeRole.Theorem),
            Node("extra-1", "Cubic phases of the six cosets", "normCoreEquiv_coordinate_residue", "The six complete rotated core cosets have alternating nontrivial cubic phases.", DescribeRole.Theorem),
            Paragraph(Text("This module supplies complete lattice counts. CubicThetaCoreProduct identifies the actual Euler quotient, CubicThetaIdentities proves the two other classical relations, and EtaSignK6 proves the full normalized sign theorem. This classical lattice mathematics carries no literature priority, unique, independent acceptance or KPI claim."))
        ), []));

    private static Formula NormTriplingFormula()
    {
        var p = F.Id("p");
        var z = Seq(Mathbb, Grp(F.Id("Z")));
        var first = Seq(p, Dot, D(1));
        var second = Seq(p, Dot, D(2));
        return Disp(Seq(Forall, Sp, p, Sp, Colon, Sp, z, Sp, Times, Sp, z, Comma, Sp,
            Operatorname, Grp(F.Id("normTripling")), Sp, p, Sp, F.Eq, Sp,
            Parenthesized(Seq(first, Sp, Minus, Sp, second, Comma, Sp,
                first, Sp, Plus, Sp, D(2), Sp, Cdot, Sp, second))));
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula NormThirdFormula()
    {
        var p = F.Id("p");
        var z = Seq(Mathbb, Grp(F.Id("Z")));
        var first = Seq(p, Dot, D(1));
        var second = Seq(p, Dot, D(2));
        return Disp(Seq(Forall, Sp, p, Sp, Colon, Sp, z, Sp, Times, Sp, z, Comma, Sp,
            Operatorname, Grp(F.Id("normThird")), Sp, p, Sp, F.Eq, Sp,
            Parenthesized(Seq(Operatorname, Grp(F.Id("Int")), Dot, Operatorname, Grp(F.Id("ediv")), Sp,
                Parenthesized(Seq(D(2), Sp, Cdot, Sp, first, Sp, Plus, Sp, second)), Sp, D(3), Comma, Sp,
                Operatorname, Grp(F.Id("Int")), Dot, Operatorname, Grp(F.Id("ediv")), Sp,
                Parenthesized(Seq(second, Sp, Minus, Sp, first)), Sp, D(3)))));
    }

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create("cubic-theta-lattice-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source, Original),
            Blocks(Paragraph(Text(prose))), role);
}
