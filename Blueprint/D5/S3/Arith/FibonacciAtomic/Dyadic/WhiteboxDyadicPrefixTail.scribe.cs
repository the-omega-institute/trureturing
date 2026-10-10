using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Dyadic;

internal sealed class WhiteboxDyadicPrefixTailDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.";
    private static Formula V(string n) => F.Id(n);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(Formula x, Formula t, Formula b) =>
        Par(Seq(Forall, Sp, x, Colon, Sp, t, Comma, Sp, b));
    private static Formula And(Formula a, Formula b) => Par(Seq(a, Sp, Land, Sp, b));
    private static Formula Imp(Formula a, Formula b) => Par(Seq(a, Sp, To, Sp, b));
    private static Formula Ex(Formula x, Formula t, Formula b) =>
        Par(Seq(Exists, Sp, x, Colon, Sp, t, Comma, Sp, b));
    private static Formula Power(Formula d) => new Formula.Power(D(2), d);
    private static Formula Sum(Formula x, Formula t, Formula b) =>
        Seq(new Formula.Subscript(F.Sum, Seq(x, Sp, InMacro, Sp, t)), b);
    private static Formula E(Formula f) => Call("E", f);
    private static DocumentBlock Thm(string n, string title, Formula f, string prose)
    {
        var declaration = n == "Paths.path_expectation"
            ? "path_expectation"
            : n == "Paths.path_law"
                ? "path_law"
                : n;
        return Describe.Lean(DescribeId.Create(n.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
            // Formal GIDs admit one final declaration selector. The resolver matches that
            // selector against the unique full Lean name, so nested Paths declarations retain
            // their full namespace in the source and narrative while using the canonical GID.
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(Disp(f)),
            n == "ddg_lower"
                ? AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Computability/lumbroso2013ddg"))
                : n == "cylinder_tail_lower"
                    ? AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/lumbroso2013ddg"))
                    : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    }

    public DocumentDefinition Create()
    {
        var m = V("m"); var d = V("d"); var i = V("i"); var a = V("a"); var t = V("t");
        var s = V("s"); var f = V("f"); var alpha = V("A"); var beta = V("B");
        var fin = Call("Fin", m); var sampler = Call("PrefixSampler", fin);
        var p = Call("law", s);
        Formula General(Formula body) => All(alpha, V("Type"), All(s, Call("PrefixSampler", alpha), body));
        Formula Finite(Formula body) => All(m, Nat, All(s, sampler, body));
        Formula Relabel(Formula body) => All(alpha, V("Type"), All(beta, V("Type"),
            All(f, Seq(alpha, Sp, To, Sp, beta), All(s, Call("PrefixSampler", alpha), body))));
        var survival = Call("active", s, d);
        var ratio = new Formula.Fraction(Call("R", p, d), Power(d));
        var path = V("g");
        Formula Paths(Formula body) => All(m, Nat, Imp(Seq(D(2), Sp, Le, Sp, m),
            All(path, V("Path"), Imp(Call("IsRootPath", m, path), body))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The same output law and the same fair-bit history determine a universal dyadic survival bound.",
            H("Fair-prefix Samplers and Dyadic Tail Costs"), Blocks(
                Paragraph(Text("A prefix sampler observes only the first d fair bits. An emitted label "
                    + "persists at every larger depth, and almost every infinite tape emits a label at "
                    + "some finite depth. The emitted event is the union of its finite stopping cylinders. "
                    + "The active event at depth d consists of prefixes that still emit no label. "
                    + "The bill is the nonnegative extended-real sum of these active indicators; it "
                    + "counts the first stopping depth and is infinite on a tape that never stops.")),
                Paragraph(Text("Write p for the output law, R(p,d)=2^d-sum_i floor(2^d p(i)), "
                    + "and L(p)=sum_d R(p,d)/2^d. Each stopped output occupies an integer number "
                    + "of depth-d cylinders. Its cylinder count is at most floor(2^d p(i)), because "
                    + "every such cylinder lies in the eventual emitted event. The remaining cylinders "
                    + "are therefore at least R(p,d). This comparison uses the joint prefix "
                    + "execution and its eventual output law.")),
                Thm("emitted_measurable", "Emission is measurable",
                    General(All(i, alpha, Call("MeasurableSet", Call("emitted", s, i)))),
                    "A countable union of finite unions of cylinders gives the emitted event."),
                Thm("emitted_disjoint", "Distinct labels are disjoint",
                    General(Call("PairwiseDisjoint", Seq(i, Sp, Mapsto, Sp, Call("emitted", s, i)))),
                    "Two finite emissions on one tape agree after both prefixes are extended to their common maximum depth."),
                Thm("law_simplex", "The common finite output law",
                    Finite(And(All(i, fin, Seq(D(0), Sp, Le, Sp, Call("law", s, i))),
                        Equal(Sum(i, fin, Call("law", s, i)), D(1)))),
                    "Almost-sure termination and disjoint emission events make p a nonnegative probability vector."),
                Thm("cylinder_tail_lower", "Every depth pays its dyadic residual",
                    Finite(All(d, Nat, Seq(Call("ofReal", ratio), Sp, Le, Sp, Call("fairTape", survival)))),
                    "The floor bound on every stopped-label cylinder count leaves at least R(p,d) active cylinders, each of mass 2^(-d)."),
                Thm("ddg_lower", "The expected bit bill dominates the dyadic cost",
                    Finite(Imp(Call("Summable", Seq(d, Colon, Sp, Nat, Sp, Mapsto, Sp, ratio)),
                        Seq(Call("ofReal", Call("L", p)), Sp, Le, Sp, E(Call("bill", s))))),
                    "Tonelli identifies the expected bill with the sum of the survival probabilities. "
                    + "Termwise cylinder bounds give the cost inequality when the real dyadic series is summable. "
                    + "This is the classical optimal random-bit cost lower bound recalled in Lumbroso, "
                    + "Section 2.1, equations (1)-(2). Its formalization here connects PrefixSampler, "
                    + "emitted, active, and bill to that cost expression on the same execution and output law."),
                Thm("relabel_emitted", "Relabelling the emitted event",
                    Relabel(All(i, beta, All(t, V("Tape"), Seq(
                        t, Sp, InMacro, Sp, Call("emitted", Call("relabel", f, s), i), Sp, Iff,
                        Sp, Ex(a, alpha, And(Seq(t, Sp, InMacro, Sp, Call("emitted", s, a)),
                            Equal(Call("f", a), i))))))),
                    "A relabelled output occurs precisely when an original output occurs and maps to that label."),
                Thm("relabel_bill", "Relabelling preserves every charged bit",
                    Relabel(Equal(Call("bill", Call("relabel", f, s)), Call("bill", s))),
                    "Mapping an emitted label preserves exactly the active prefixes, including every exceptional infinite path."),
                Thm("relabel_law_equiv", "A label permutation transports the law",
                    Finite(All(V("e"), Call("Perm", fin), All(i, fin,
                        Equal(Call("law", Call("relabel", V("e"), s), i),
                            Call("law", s, Call("inverse", V("e"), i)))))),
                    "The emission event for a permuted label equals the original event for its inverse image."),
                Thm("bill_measurable", "The extended bit bill is measurable",
                    General(Call("Measurable", Call("bill", s))),
                    "The bill is a countable nonnegative sum of measurable active indicators."),
                Thm("Paths.path_expectation", "The finite observer preserves expected code length",
                    Paths(Equal(E(Call("bill", Call("fromPath", m, path))), Call("ofReal", Call("pathCost", path)))),
                    "The observer stops at the unique labelled leaf contained in its finite prefix. "
                    + "The public carry-tree stopping-word contract gives its first stopping length "
                    + "and almost-sure return, so its expected charge equals the path cost. "
                    + "The canonical path_expectation selector resolves to the unique Lean constant "
                    + "D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail.Paths.path_expectation."),
                Thm("Paths.path_law", "The finite observer preserves the digit law",
                    Paths(All(i, fin, Equal(Call("law", Call("fromPath", m, path), i),
                        Call("ofDigits", Call("labelDigit", path, i))))),
                    "The observer emits i exactly on the public carry-tree event of a finite return with label i. "
                    + "Its probability is the fixed-label binary digit series. "
                    + "The canonical path_law selector resolves to the unique Lean constant "
                    + "D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail.Paths.path_law."))));
    }
}
