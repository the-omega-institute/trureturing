using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class QutritChannelUnitaryExtremeDecompositionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/QutritChannelUnitaryExtremeDecomposition";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/Eigenstructure/haagerupmusatruskai2021extreme");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every equal-modulus Haagerup–Musat–Ruskai qutrit channel is a mixture of a unitary conjugation and a rank-three channel extreme in both the unital and trace-preserving completely positive maps.",
        H("Unitary and doubly extreme decomposition of a qutrit channel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hmr-kraus"),
                DeclarationHandle.Create(Module + ".hmrKraus"),
                H("The four HMR operators"),
                StatementSource.FromAuthor(Disp(KrausFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The four matrices are the operators A₁, A₂, A₃, A₄ of Theorem UCPT, "
                    + "HMR2021J.tex lines 280–285, in that order. The vector notation ![A₁,A₂,A₃,A₄] "
                    + "is a function on Fin 4, with indices zero through three. The star on a complex "
                    + "entry is complex conjugation. This definition allows arbitrary complex α and β; "
                    + "the source's channel theorem assumes |α|² + |β|² = 1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hmr-channel"),
                DeclarationHandle.Create(Module + ".hmrChannel"),
                H("The HMR matrix map"),
                StatementSource.FromAuthor(Disp(ChannelFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "This is the complex linear map Φ in HMR2021J.tex line 286. "
                    + "MatrixMap.of_kraus K L sends ρ to the sum of K(k)ρL(k)*. "
                    + "Both families here are k ↦ A(k)*, so the action is one half of the sum "
                    + "of A(k)*ρA(k). In particular, the adjoints occur on the left. "
                    + "The scalar one half is complex. The definition imposes no modulus condition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("is-unital"),
                DeclarationHandle.Create(Module + ".IsUnital"),
                H("Preserving the identity"),
                StatementSource.FromAuthor(Disp(UnitalFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A complex linear map on three-by-three matrices is unital precisely when "
                    + "it maps the identity matrix to the identity matrix. Together with complete "
                    + "positivity this is the UCP condition used in HMR2021J.tex lines 377–383."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The decomposition for all equal-modulus parameters"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For every pair of complex parameters of norm 1/√2, the channel is a "
                        + "convex combination of a unitary conjugation and a completely positive, "
                        + "unital, trace-preserving map ψ. Its Choi matrix has natural-valued rank "
                        + "three, and ψ is separately extreme in the UCP maps and in the CPT maps, "
                        + "where convexity is over the real scalars. The equality holds for every "
                        + "complex matrix ρ. MatrixMap.choi_matrix is the Choi matrix operation; "
                        + "MatrixMap.IsCompletelyPositive quantifies over every finite amplification, "
                        + "and MatrixMap.IsTracePreserving requires preservation of the trace of every "
                        + "matrix. Complex.ofReal displays both real-to-complex coefficient casts. "
                        + "The source's question is HMR2021J.tex lines 387–390; its positive real "
                        + "parameter example is at lines 366–383. The construction below always takes lam = 1/4.")),
                    Paragraph(Text(
                        "First consider any three matrices y(i) and their map "
                        + "Ψ(ρ) = Σᵢ y(i)*ρy(i). If Ψ = tθ + sη with t > 0, s ≥ 0 "
                        + "and θ, η completely positive, then C(Ψ) − tC(θ) = sC(η) is positive "
                        + "semidefinite. Positivity implies ker C(Ψ) ⊆ ker C(θ). "
                        + "Let V have columns given by the entries of y(i)*, so C(Ψ) = VV*. "
                        + "Factor C(θ) = BB*. The kernel inclusion gives B* = QC(Ψ) for a matrix Q, "
                        + "hence C(θ) = VHV* with H = V*Q*QV. Inverting the Choi correspondence "
                        + "gives θ(ρ) = Σᵢⱼ Hᵢⱼ y(i)*ρy(j).")),
                    Paragraph(Text(
                        "Suppose Σᵢ y(i)*y(i) = I and the nine products y(i)*y(j) are complex "
                        + "linearly independent. Unitality of θ then makes H equal to I by uniqueness "
                        + "of coefficients, so θ = Ψ. This proves extremality among UCP maps. "
                        + "For CPT maps, assume Σᵢ y(i)y(i)* = I and independence of the nine "
                        + "products y(i)y(j)*. Trace preservation, cyclicity of trace and the "
                        + "nondegenerate trace pairing give Σᵢⱼ Hᵢⱼ y(j)y(i)* = I. "
                        + "Coefficient uniqueness applied to the transpose of H again gives H = I. "
                        + "Independence of y(i)*y(j) also implies independence of the three y(i), "
                        + "then of their adjoints and of the columns of V. Thus rank C(Ψ) = "
                        + "rank(VV*) = rank V = 3.")),
                    Paragraph(Text(
                        "Put q = √2, viewing the real entries below as complex numbers. "
                        + "Choose the three y(i), in order, to be 1/(2√3) times "
                        + "the matrices [[−1,−q,1],[q,0,−q],[−1,q,1]], "
                        + "[[1,q,1],[q,0,q],[1,q,1]], and "
                        + "[[1,−q,1],[−q,0,q],[−1,q,−1]]. "
                        + "Entrywise multiplication verifies both sums of products equal I. "
                        + "For each of the two nine-product families, explicit dual coordinate "
                        + "matrices recover each coefficient from any linear combination of the "
                        + "products: the sum of the entrywise products with the chosen dual matrix "
                        + "is that coefficient. Applying these identities to a zero linear combination "
                        + "proves both independence assertions. These calculations use (√2)² = 2, "
                        + "(√3)² = 3 and √3 ≠ 0. Consequently the map Ψ₀ associated with these "
                        + "three matrices has both extremality properties and Choi rank three.")),
                    Paragraph(Text(
                        "Write Φ₀ for the channel at α = β = 1/√2, and set "
                        + "U₀ = 1/2 [[1,−q,−1],[q,0,q],[−1,−q,1]]. "
                        + "Direct calculation of its nine entries proves U₀*U₀ = I. "
                        + "Expanding the two Kraus sums entry by entry proves, for every ρ, "
                        + "Φ₀(ρ) = (1/4)U₀*ρU₀ + (3/4)Ψ₀(ρ). "
                        + "These matrices are the source's operators 2X₂ and (2/√3)(X₁,X₃,X₄), "
                        + "respectively, from HMR2021J.tex lines 370–381.")),
                    Paragraph(Text(
                        "For general α and β of the required norms, set u = √2 α and v = √2 β. "
                        + "Both have norm one. Choose a fifth root r with r⁵ = uv² and set "
                        + "s = r²/v. Norm multiplicativity gives |r| = |s| = 1, and algebra gives "
                        + "rs² = u and r²/s = v. The diagonal matrices D = diag(r,1,r⁻¹) and "
                        + "E = diag(s,1,s⁻¹) are unitary. Substituting these identities in the "
                        + "nine entries of the Kraus sums gives Φα,β(ρ) = E*Φ₀(D*ρD)E.")),
                    Paragraph(Text(
                        "The transformation T(φ)(ρ) = E*φ(D*ρD)E preserves complete positivity "
                        + "by composition of Kraus maps. Unitarity gives unitality, and cyclicity "
                        + "of trace gives trace preservation. Its inverse uses D* and E*. "
                        + "Together these transformations form a real linear equivalence mapping "
                        + "each of the UCP and CPT sets onto itself; the image theorem for extreme "
                        + "points therefore preserves each extremality property. In Choi coordinates "
                        + "C(T(φ)) = QC(φ)Q*, where Q has entries "
                        + "Q((a,i),(b,j)) = conjugate(E(b,a)) conjugate(D(i,j)). "
                        + "The rank of a product cannot exceed that of its middle factor. "
                        + "Applying this inequality to T and its inverse proves equality of Choi ranks.")),
                    Paragraph(Text(
                        "Transport the positive real parameter decomposition by T. The unitary "
                        + "term becomes conjugation by U = DU₀E, and the other term becomes "
                        + "ψ = T(Ψ₀), which retains complete positivity, unitality, trace preservation, "
                        + "rank three and both extremality properties. With lam = 1/4 the two "
                        + "nonnegative weights are 1/4 and 3/4, and their sum is one. "
                        + "The phase identity identifies the transported channel with Φα,β, "
                        + "giving the stated equality on every ρ."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("haagerup-musat-ruskai-2021-qutrit-channel-unitary-extreme-decomposition"),
                    ResolutionKind.Proved)))));

    private static Formula KrausFormula()
    {
        Formula z = Typed(D(0), Complexes()), o = Typed(D(1), Complexes());
        Formula family = Seq(Bang, OpenBracket,
            MatrixLiteral(X("α"), z, z, z, z, o, z, z, z), Comma, Sp,
            MatrixLiteral(z, z, X("β"), z, z, z, z, o, z), Comma, Sp,
            MatrixLiteral(z, new Formula.Negate(o), z, z, z, z,
                new Formula.Negate(StarOf(X("β"))), z, z), Comma, Sp,
            MatrixLiteral(z, z, z, o, z, z, z, z, StarOf(X("α"))), CloseBracket);
        return All("α", Complexes(), All("β", Complexes(),
            Equal(Typed(LocalCall("hmrKraus", X("α"), X("β")),
                Arrow(FinOf(D(4)), MatrixType())), family)));
    }

    private static Formula ChannelFormula()
    {
        Formula family = LambdaOf("k", FinOf(D(4)),
            StarOf(LocalCall("hmrKraus", X("α"), X("β"), X("k"))));
        return All("α", Complexes(), All("β", Complexes(),
            Equal(Typed(LocalCall("hmrChannel", X("α"), X("β")), MapType()),
                Smul(Typed(new Formula.Fraction(D(1), D(2)), Complexes()),
                    At(Underscored("MatrixMap", "of", "kraus"), family, family)))));
    }

    private static Formula UnitalFormula() => All("φ", MapType(),
        IffOf(LocalCall("IsUnital", X("φ")),
            Equal(At(X("φ"), Typed(D(1), MatrixType())), Typed(D(1), MatrixType()))));

    private static Formula ResultFormula()
    {
        Formula norm = new Formula.Fraction(Typed(D(1), Reals()),
            At(Qualified("Real", "sqrt"), Typed(D(2), Reals())));
        Formula equation = All("ρ", MatrixType(),
            Equal(LocalCall("hmrChannel", X("α"), X("β"), X("ρ")),
                Add(Smul(OfReal(X("lam")), Mul(Mul(StarOf(X("u")), X("ρ")), X("u"))),
                    Smul(OfReal(Sub(Typed(D(1), Reals()), X("lam"))), At(X("ψ"), X("ρ"))))));
        Formula conditions = Conjoin(
            Member(X("u"), At(Qualified("Matrix", "unitaryGroup"), FinOf(D(3)), Complexes())),
            LE(Typed(D(0), Reals()), X("lam")),
            LE(X("lam"), Typed(D(1), Reals())),
            CP(X("ψ")), LocalCall("IsUnital", X("ψ")), TP(X("ψ")),
            Equal(At(Qualified("Matrix", "rank"),
                At(Underscored("MatrixMap", "choi", "matrix"), X("ψ"))), Typed(D(3), Naturals())),
            Extreme(X("ψ"), LocalCall("IsUnital", X("θ"))),
            Extreme(X("ψ"), TP(X("θ"))), equation);
        return All("α", Complexes(), All("β", Complexes(),
            Arrow(Equal(new Formula.Norm(X("α")), norm),
            Arrow(Equal(new Formula.Norm(X("β")), norm),
                Some("u", MatrixType(), Some("lam", Reals(), Some("ψ", MapType(), conditions)))))));
    }

    private static Formula Extreme(Formula map, Formula property) => Member(map,
        At(Qualified("Set", "extremePoints"), Reals(),
            Seq(OpenBrace, Typed(X("θ"), MapType()), Sp, Mid, Sp,
                And(CP(X("θ")), property), CloseBrace)));
    private static Formula CP(Formula map) => At(Qualified("MatrixMap", "IsCompletelyPositive"), map);
    private static Formula TP(Formula map) => At(Qualified("MatrixMap", "IsTracePreserving"), map);
    private static Formula OfReal(Formula value) => At(Qualified("Complex", "ofReal"), value);
    private static Formula StarOf(Formula value) => At(Qualified("star"), value);
    private static Formula MatrixType() => At(Qualified("Matrix"), FinOf(D(3)), FinOf(D(3)), Complexes());
    private static Formula MapType() => At(Qualified("MatrixMap"), FinOf(D(3)), FinOf(D(3)), Complexes());
    private static Formula MatrixLiteral(Formula a, Formula b, Formula c, Formula d, Formula e,
        Formula f, Formula g, Formula h, Formula i) => Seq(Begin, Grp(F.Id("pmatrix")),
            a, Amp, b, Amp, c, RowBreak, d, Amp, e, Amp, f, RowBreak, g, Amp, h, Amp, i,
            End, Grp(F.Id("pmatrix")));
    private static Formula LocalCall(string name, params Formula[] args) => At(Qualified(
        "D5", "S3", "Quantum", "QuantumChannels", "QutritChannelUnitaryExtremeDecomposition", name), args);
    private static Formula X(string name) => name switch
    {
        "α" => Alpha, "β" => Beta, "φ" => Varphi, "ψ" => Psi, "ρ" => Rho, "θ" => Theta,
        _ => F.Id(name),
    };
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Underscored(string owner, string first, string second) =>
        Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(first), Underscore, Grp(F.Id(second))));
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Smul(Formula scalar, Formula value) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(value));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(
        Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(
        Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Conjoin(params Formula[] values)
    {
        Formula result = values[^1];
        for (int i = values.Length - 2; i >= 0; i--) result = And(values[i], result);
        return result;
    }
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(
        Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
}
