using System.Collections.Immutable;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;
internal sealed class HilbertTraceClassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Intrinsic CFC trace class and basis-independent positive trace on arbitrary complex Hilbert spaces.",
        H("Hilbert Trace Class and Positive Trace"),
        Blocks(
            Paragraph(Text("This module is an A17.2 source transplant of seven declarations from Tom Ole Diem’s physlib TraceClass/Basic at revision 0aeb3dc7e249f9acc9032252060d4fa5f35c7e20. The upstream declaration statements and proofs are retained; this is known mathematics and carries no claim of a new theorem or independent proof. The complete Apache 2.0 license is in docs/reports/hilbert-trace-class/physlib-LICENSE.txt. The verified immutable upstream tree has no NOTICE file.")),
            Describe.Lean(DescribeId.Create("istraceclass"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/HilbertTraceClass.IsTraceClass"),
            H("Intrinsic trace class"), StatementSource.FromAuthor(Statement("IsTraceClass")), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The predicate asks for one set-indexed Hilbert basis whose real diagonal of CFC.abs T is summable. CFC.abs is the continuous-functional-calculus square root of the adjoint-product operator. No finite dimension, separability, chosen physical basis or positivity premise is added."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hassum-norm-sq-inner-basis"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/HilbertTraceClass.hasSum_norm_sq_inner_basis"),
            H("Parseval in a set-indexed Hilbert basis"), StatementSource.FromAuthor(Statement("hasSum_norm_sq_inner_basis")), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For an arbitrary vector y, the sum of squared norms of its complex inner products with the Hilbert basis equals the squared norm of y. This lemma omits the completeness assumption. The proof takes real parts of the pinned HilbertBasis inner-product sum; it is consumed by the self-adjoint norm-square comparison."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("hassum-norm-sq-apply-of-selfadjoint"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/HilbertTraceClass.hasSum_norm_sq_apply_of_selfAdjoint"),
            H("Basis independence of the squared image norms"), StatementSource.FromAuthor(Statement("hasSum_norm_sq_apply_of_selfAdjoint")), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For a bounded self-adjoint S and two arbitrary Hilbert bases, summability of the squared image norms in the first basis yields HasSum in the second basis with the first basis sum. The original nonnegative double-series and Parseval argument is retained. This is used by absolute-diagonal summability and the positive trace formula."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("summable-inner-abs-of-hilbertbasis"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/HilbertTraceClass.summable_inner_abs_of_hilbertBasis"),
            H("Absolute-diagonal summability in every basis"), StatementSource.FromAuthor(Statement("summable_inner_abs_of_hilbertBasis")), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("An intrinsically trace-class bounded operator has a summable real diagonal of its CFC absolute value in every Hilbert basis. The proof applies the self-adjoint comparison to the positive square root of CFC.abs T, retaining the actual operator meaning of trace class."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("trace"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/HilbertTraceClass.trace"),
            H("Complex trace from a trace-class witness"), StatementSource.FromAuthor(Statement("trace")), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The trace is the complex diagonal sum in the Hilbert basis selected by the trace-class witness. The positive trace theorem below identifies this value with the sum in every other Hilbert basis. No unrestricted non-self-adjoint basis-independence claim is made."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("summable-inner-of-nonneg"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/HilbertTraceClass.summable_inner_of_nonneg"),
            H("Complex summability for positive operators"), StatementSource.FromAuthor(Statement("summable_inner_of_nonneg")), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Positivity makes the diagonal real and identifies CFC.abs T with T. The theorem converts the real absolute-diagonal summability into complex diagonal summability in every arbitrary Hilbert basis. Its full intrinsic trace-class and positivity hypotheses remain explicit."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("trace-eq-of-hilbertbasis-of-nonneg"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/HilbertTraceClass.trace_eq_of_hilbertBasis_of_nonneg"),
            H("Positive trace in every Hilbert basis"), StatementSource.FromAuthor(Statement("trace_eq_of_hilbertBasis_of_nonneg")), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For a positive bounded trace-class operator, the witness-defined trace equals the complex diagonal sum in every Hilbert basis. The proof compares square-root norm sums across the witness and target bases. Zero spaces and zero operators remain in the universal domain."))), DescribeRole.Lemma),
            Paragraph(Text("The receiver remains on its own Lean v4.33.0 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d pins. Retirement is decided only at the receiver’s adopted pin: an explicit finite replacement map must supply the same intrinsic predicate, trace and theorem telescopes, and all live consumer applications and standard-axiom checks must pass. Then consumers are replaced and this transplant is removed in the same change. An external merge or an unpinned release is not a retirement trigger.")),
            Paragraph(Text("For a physical positive heat operator B, a diagonal HasSum in the physical Hermite basis can construct the intrinsic trace-class witness after reindexing the basis by its range. The positive trace formula then transfers that sum to every Hilbert basis. The same argument applies to the positive scalar-normalized Gibbs operator after scaling its diagonal sum. Those are consumer applications requiring their own exact checks; this supplier alone does not establish a partition function, physical tensor factorization, metaplectic realization or the whole parent theorem.")))));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [new(FormulaIdentifier.Create(name), type)], body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [new(FormulaIdentifier.Create(name), type)], body);
    private static Formula Map(string name, Formula type, Formula body) =>
        Seq(Open, F.Id(name), Colon, Sp, type, Sp, Mapsto, Sp, body, Close);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Statement(string name)
    {
        Formula hspace = F.Id("H"), t = F.Id("T"), s = F.Id("S"), w = F.Id("w"), v = F.Id("v");
        Formula b = F.Id("b"), c = F.Id("c"), y = F.Id("y"), i = F.Id("i"), j = F.Id("j"), h = F.Id("h");
        Formula complex = Seq(Mathbb, Grp(F.Id("C"))), real = Seq(Mathbb, Grp(F.Id("R")));
        Formula set = Call("Set", hspace), index = Call("Subtype", w), otherIndex = Call("Subtype", v);
        Formula op = Call("ContinuousLinearMap", complex, hspace, hspace);
        Formula Basis(Formula x) => Call("HilbertBasis", Call("Subtype", x), complex, hspace);
        Formula NormSq(Formula x) => Call("pow", Call("norm", x), D(2));
        Formula Diag(Formula basis, Formula oper, Formula k) => Call("innerC", Apply(basis, k), Apply(oper, Apply(basis, k)));
        Formula AbsDiag(Formula basis, Formula k) => Call("re", Diag(basis, Call("CfcAbs", t), k));
        Formula TC(Formula oper) => Call("IsTraceClass", oper);
        Formula Sum(Formula family) => Call("tsum", family);
        Formula Positive(Formula oper) => Seq(D(0), Sp, Le, Sp, oper);
        Formula InBasis(Formula body) => All("w", set, All("b", Basis(w), body));
        Formula WithTraceClass(Formula body, bool positive) => All("T", op,
            positive ? All("hT", Positive(t), All("h", TC(t), body)) : All("h", TC(t), body));
        Formula body;
        if (name == "IsTraceClass")
        {
                body = All("T", op, new Formula.Logic(TC(t), FormulaLogicOperator.Iff,
                    Exists("w", set, Exists("b", Basis(w),
                        Call("Summable", Map("i", index, AbsDiag(b, i)))))));
        }
        else if (name == "hasSum_norm_sq_inner_basis")
        {
                body = InBasis(All("y", hspace,
                    Call("HasSum", Map("i", index, NormSq(Call("innerC", Apply(b, i), y))), NormSq(y))));
        }
        else if (name == "hasSum_norm_sq_apply_of_selfAdjoint")
        {
                body = All("S", op, All("hS", Call("IsSelfAdjoint", s),
                    All("w", set, All("v", set, All("b", Basis(w), All("c", Basis(v),
                    All("hb", Call("Summable", Map("i", index, NormSq(Apply(s, Apply(b, i))))),
                        Call("HasSum", Map("j", otherIndex, NormSq(Apply(s, Apply(c, j)))),
                            Sum(Map("i", index, NormSq(Apply(s, Apply(b, i)))))))))))));
        }
        else if (name == "summable_inner_abs_of_hilbertBasis")
        {
                body = WithTraceClass(InBasis(Call("Summable", Map("i", index, AbsDiag(b, i)))), false);
        }
        else if (name == "summable_inner_of_nonneg")
        {
                body = WithTraceClass(InBasis(Call("Summable", Map("i", index, Diag(b, t, i)))), true);
        }
        else if (name == "trace_eq_of_hilbertBasis_of_nonneg")
        {
                body = WithTraceClass(InBasis(Equal(Call("trace", t, h), Sum(Map("i", index, Diag(b, t, i))))), true);
        }
        else if (name == "trace")
        {
                Formula witnessSet = Call("choose", h);
                Formula witnessBasis = Call("choose", Call("chooseSpec", h));
                body = WithTraceClass(Equal(Call("trace", t, h),
                    Sum(Map("i", Call("Subtype", witnessSet), Diag(witnessBasis, t, i)))), false);
        }
        else throw new System.ArgumentException(name);
        if (name != "hasSum_norm_sq_inner_basis") body = All("complete", Call("CompleteSpace", hspace), body);
        body = All("inner", Call("InnerProductSpace", complex, hspace), body);
        body = All("normed", Call("NormedAddCommGroup", hspace), body);
        return All("H", Call("Type", F.Id("u")), body);
    }
}
