using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class SchurChannelMixedUnitaryDistanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/yuduanxu2017unitarydistance");
    private const string Question = "It seems quite likely that in Eq. (8) the first inequality should be strict and the second one should be an equality. However, this is still an unsettled issue.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every Schur channel, the diamond distance to all mixed-unitary channels equals the distance to Schur mixed-unitary channels.",
        H("Schur-channel mixed-unitary distance equality"),
        Blocks(
            Node("MixedUnitary", "Finite convex mixtures of unitary channels", MixedFormula(),
                "Page 1: \"So any Ψ ∈ Conv(U(H_d)) can be written as a mixture (convex combination) of unitary channels. (The number of unitary channels in the mixture can be made finite due to the Carathéodory’s theorem on convex hull).\" The dimension d and mixture length n are natural numbers. The real weights p are nonnegative and sum to one. U is a family in Matrix.unitaryGroup; val exposes each matrix, star is its matrix adjoint, and act is the canonical channel action on every complex matrix X.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsSchurChannel", "Entrywise channel action", SchurFormula(),
                "Section II, page 4: \"For any S ∈ L(H_d), we can define a super-operator Φ_S via the following way:\" followed by Φ_S(X) = S ◦ X, ∀X ∈ L(H_d), and \"where S ◦ X = [s_kj x_kj] is the entry-wise product or Hadamard product.\" Here Psi already is a completely positive trace-preserving channel, and its action on every X is Matrix.hadamard C X. Complete positivity and trace preservation supply the source's matrix conditions.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("SchurMixedUnitary", "Schur channels that are unitary mixtures", SchurMixedFormula(),
                "Section V, page 8, defines Λ(H_d) = S(H_d) ∩ Conv(U(H_d)) and states: \"Intuitively, Λ(H_d) (or simply Λ_d) is the set of Schur channels that are also mixtures of diagonal unitary channels. So any Ψ ∈ Λ_d can be written into the form Ψ = Σ_k p_k U_k · U_k†, where U_k are d × d diagonal unitary matrices.\" The displayed set requires both Schur action and membership in MixedUnitary d.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("distToSet", "Diamond distance to a set of channels", DistanceFormula(),
                "Page 1 defines D(Phi, Conv(U(H))) as the infimum of D(Phi, Psi) over Psi in Conv(U(H)), and states: \"where D(Φ, Ψ) will be given by the diamond norm of Φ − Ψ.\" Here S is any set of channels on Fin d. Set.image collects the unhalved FiniteDiamondDistance.diamondDistance values; sInf is the real infimum. The theorem uses nonempty sets whose values are bounded below.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The equality asked after Equation (8)", ClaimFormula(),
                "Section V, page 9, after the proof of Theorem 3: \"" + Question + "\" This proposition states the equality in the second inequality. d ranges over all natural dimensions, Phi over canonical channels on Fin d, and IsSchurChannel is the sole hypothesis. MixedUnitary represents Conv(U_d), and SchurMixedUnitary represents Λ_d. The empty dimension is included; both sets still contain the identity channel.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("reindex_traceNorm", "Trace norm is invariant under finite reindexing", ReindexTraceNormFormula(),
                "For finite decidable index types a and b, an equivalence e preserves the trace norm under Matrix.reindexAlgEquiv. This identity also gives the submatrix form for the inverse equivalence, and it identifies ancillary coordinates in the capacity bounds.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "The two diamond-distance infima are equal", Disp(Named("claim")),
                "Copy a basis vector i to (i,i), apply the channel on the first factor while retaining the second, and recover coherently from the correlated subspace. On its complement, recovery maps (k,i) to i. These Kraus operators sum to a trace-preserving channel. The resulting superchannel fixes every Schur channel and contracts diamond distance. Each diagonal entry of a unitary is the midpoint of two unit complex phases; independent choices of those phases give a uniform family of 2^d diagonal unitaries. Thus every unitary mixture has a Schur unitary mixture at no greater distance from Phi. Set inclusion gives the opposite inequality. This proves equality of infima without requiring an attained minimum. Pointwise recovery errors need only satisfy the contraction inequality. The argument gives no closed form for the common distance. Relating positive distance to nonmembership requires compactness or closedness beyond the present theorem. The amplified contraction estimates in this proof also have a finite-window channel application. Let A, B and C be independent finite decidable coordinate types, C1:A->B and C2:B->C canonical CPTP channels, and PA, PB and PC arbitrary specified real-time CPTP families. For a,b>0 and T>=0 define e_T(C1;a) as one half of the supremum, over 0<=t<=T, of the unhalved stabilized diamondDistance between C1 comp PA(t) and PB(a*t) comp C1; use the analogous definition for the other channels. The stabilization tests every finite reference dimension and every joint density input, including correlated inputs. The existing diamond_bounds bounds the distances by two; adjoining zero defines empty windows and does not change a nonnegative-horizon supremum, since t=0 belongs to the window. Thus 0<=e_T<=1. For a common joint input rho, insert the output of C2 comp PB(a*t) comp C1 between those of C2 comp C1 comp PA(t) and PC((a*b)*t) comp C2 comp C1. The existing traceDistance_triangle splits the error. Applying trace_contract_rectangular to referenceChannel C2 bounds the first term by the first channel error on rho. For the second term use the density state obtained from rho by referenceChannel C1; reference_error_le_diamond bounds it by the stabilized error of C2 at time a*t. The two bounded time suprema, 0<=a*t<=a*T and b*(a*t)=(a*b)*t yield e_T(C2 comp C1;a*b)<=e_T(C1;a)+e_(a*T)(C2;b), with the factor one half applied to the unhalved estimates. This includes T=0 and empty coordinate types through the zero convention; no identity at time zero, maximum attainment, semigroup, continuity, generator, recovery or locality is assumed. This application uses the existing estimates; the Schur-channel equality itself requires its stated Schur hypothesis. A complete application to actual rectangular stochastic channels and stochastic evolution requires their canonical CPTP realization and the corresponding diagonal relative-entropy identification. That realization is not established here. Channel composition alone supplies no RG universality or effective dynamics, and its residual estimate does not guarantee recovery of a specified state family.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("yu-duan-xu-2017-schur-channel-diamond-equality"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("ydx-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imply(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Channel(Formula d) => Call("QuantumChannel", Call("Fin", d), Call("Fin", d));
    private static Formula MatrixType(Formula d) => Call("Matrix", Call("Fin", d), Call("Fin", d), Complexes());
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id(name), Colon, Sp, type), Sp, body);

    private static Formula ReindexTraceNormFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), e = F.Id("e"), x = F.Id("X");
        Formula matrix = Call("Matrix", a, a, Complexes());
        Formula instances = Seq(OpenBracket, Call("Fintype", a), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", a), CloseBracket, Sp,
            OpenBracket, Call("Fintype", b), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", b), CloseBracket, Sp);
        Formula equiv = Call("Equiv", a, b);
        Formula norm(Formula value) => Call("traceNorm", value);
        Formula indexed = App(App(Qualified("Matrix", "reindexAlgEquiv"), Complexes(), Complexes(), e), x);
        return Disp(All("a", Named("Type"), All("b", Named("Type"), Seq(instances,
            All("e", equiv, All("X", matrix, Equal(norm(indexed), norm(x))))))));
    }

    private static Formula MixedFormula()
    {
        Formula d = F.Id("d"), psi = F.Id("Psi"), n = F.Id("n"), p = F.Id("p"), u = F.Id("U"), k = F.Id("k"), x = F.Id("X");
        Formula uk = Call("val", App(u, k));
        Formula sandwich = new Formula.Binary(new Formula.Binary(uk, FormulaBinaryOperator.Multiply, x), FormulaBinaryOperator.Multiply, Call("star", uk));
        Formula pk = Parenthesized(Seq(App(p, k), Colon, Sp, Complexes()));
        Formula sum = SumOver("k", Call("Fin", n), Seq(pk, Sp, Cdot, Sp, Parenthesized(sandwich)));
        Formula body = Some("n", Naturals(), Some("p", Arrow(Call("Fin", n), Reals()),
            Some("U", Arrow(Call("Fin", n), App(Qualified("Matrix", "unitaryGroup"), Call("Fin", d), Complexes())),
                And(All("k", Call("Fin", n), new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, App(p, k))),
                    And(Equal(SumOver("k", Call("Fin", n), App(p, k)), D(1)),
                        All("X", MatrixType(d), Equal(Call("act", psi, x), sum)))))));
        return Disp(All("d", Naturals(), Equal(Call("MixedUnitary", d),
            Seq(OpenBrace, psi, Colon, Sp, Channel(d), Sp, Mid, Sp, body, CloseBrace))));
    }

    private static Formula SchurFormula()
    {
        Formula d = F.Id("d"), psi = F.Id("Psi"), c = F.Id("C"), x = F.Id("X");
        Formula rhs = Some("C", MatrixType(d), All("X", MatrixType(d),
            Equal(Call("act", psi, x), App(Qualified("Matrix", "hadamard"), c, x))));
        return Disp(All("d", Naturals(), All("Psi", Channel(d),
            new Formula.Logic(Call("IsSchurChannel", psi), FormulaLogicOperator.Iff, Parenthesized(rhs)))));
    }

    private static Formula SchurMixedFormula()
    {
        Formula d = F.Id("d"), psi = F.Id("Psi");
        return Disp(All("d", Naturals(), Equal(Call("SchurMixedUnitary", d),
            Seq(OpenBrace, psi, Colon, Sp, Channel(d), Sp, Mid, Sp,
                And(Call("IsSchurChannel", psi), Member(psi, Call("MixedUnitary", d))), CloseBrace))));
    }

    private static Formula DistanceFormula()
    {
        Formula d = F.Id("d"), phi = F.Id("Phi"), psi = F.Id("Psi"), s = F.Id("S");
        Formula f = Seq(Operatorname, Grp(F.Id("fun")), Sp,
            Parenthesized(Seq(psi, Colon, Sp, Channel(d))), Sp, Mapsto, Sp,
            App(Qualified("FiniteDiamondDistance", "diamondDistance"), phi, psi));
        return Disp(All("d", Naturals(), All("Phi", Channel(d), All("S", Call("Set", Channel(d)),
            Equal(Call("distToSet", phi, s), Call("sInf", App(Qualified("Set", "image"), Parenthesized(f), s)))))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d"), phi = F.Id("Phi");
        Formula body = All("d", Naturals(), All("Phi", Channel(d),
            Imply(Call("IsSchurChannel", phi), Equal(Call("distToSet", phi, Call("MixedUnitary", d)),
                Call("distToSet", phi, Call("SchurMixedUnitary", d))))));
        return Disp(new Formula.Logic(Named("claim"), FormulaLogicOperator.Iff, Parenthesized(body)));
    }
}
