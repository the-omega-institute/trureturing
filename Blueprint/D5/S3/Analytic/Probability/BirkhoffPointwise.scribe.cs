using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class BirkhoffPointwiseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real integrable time averages of an ergodic probability transformation converge almost everywhere to their integral.",
        H("Birkhoff pointwise ergodic theorem"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("birkhoff-pointwise-ergodic"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BirkhoffPointwise.birkhoff_pointwise_ergodic"),
                H("Almost-everywhere convergence to the mean"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/durrett2019probability")),
                Blocks(
                    Paragraph(Text("The carrier alpha ranges over every universe u and has an arbitrary measurable-space structure. The measure mu is any probability measure. Ergodic(T,mu) is the native conjunction of measure preservation and pre-ergodicity: every null-measurable almost-invariant set is null or conull. The real observable g is only assumed integrable. No pointwise measurability, boundedness, square integrability, countability, standard Borel structure, or invertibility is required.")),
                    Paragraph(Text("For each fixed g, the conclusion holds for mu-almost every x along the complete sequence of natural times. The average at n=0 is canonically zero; for positive n it is the sum of g(T^j x) over j<n divided by n. The theorem retains empty-carrier quantification and all integrable constants, including zero. It asserts neither a common exceptional set for every g nor uniform, vector-valued, nonergodic conditional-expectation, or L1 convergence.")),
                    Paragraph(Text("For a measurable integrable f, take the finite maximum of its initial orbit sums, including the zeroth sum. Positivity of that maximum gives a one-step inequality. Integrating over its positive set, measure preservation cancels the full integrals of the maximum and its composition with T. An increasing-set limit yields the nonnegative integral of f over the set where some orbit sum is positive.")),
                    Paragraph(Text("For each level c above the mean of g, form the invariant set where orbit sums exceed n times a rational level above c arbitrarily late. Apply the maximal integral inequality to the indicator of this set times g-c. Ergodicity makes the set null or conull; the conull case contradicts the negative integral of g-c. Countably many rational levels for g and -g give the upper and lower eventual bounds, hence order convergence. Finally, an almost-everywhere equal measurable representative has the same integral, and quasi-measure preservation identifies every finite-time average almost everywhere.")),
                    Paragraph(Text("Durrett, Probability: Theory and Examples, fifth edition, Section 6.2, Theorem 6.2.1 and Lemma 6.2.2, printed pages 335–337, provide the classical mathematical reference. The Lean proof is an attributed adaptation of facebookresearch/atlas-lean, MathlibExt/Dynamics/Ergodic/Birkhoff.lean, revision a60759060b5616df0d5775b42da4d337719feb32. Its Meta Platforms copyright and complete supplier license are retained. The adaptation makes auxiliary declarations private and uses pinned Mathlib fixed-set iteration and almost-everywhere transport; the literature note separates the book citation from the code provenance.")),
                    Paragraph(Text("Symbolic frequencies, joint-product moments, context-dependent compositions and entropy-production rates require an actual probability law, ergodicity, an integrable observable, identification of its integral and the relevant orbit or boundary correspondence. This autonomous theorem supplies the convergence step once those mathematical bridges are established."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => name switch
    {
        "alpha" => Alpha,
        "mu" => Mu,
        _ => F.Id(name)
    };
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Instance(Formula type) => Seq(OpenBracket, type, CloseBracket, Sp);
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Par(Seq(V(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Statement()
    {
        var integral = Call("integral", V("mu"), LambdaOf("y", V("alpha"), App(V("g"), V("y"))));
        var sequence = LambdaOf("n", Nat,
            Call("birkhoffAverage", Real, V("T"), V("g"), V("n"), V("x")));
        var convergence = Call("Tendsto", sequence, Named("atTop"), Call("nhds", integral));
        var ae = Call("Eventually", LambdaOf("x", V("alpha"), convergence), Call("ae", V("mu")));
        return Disp(new Formula.Aligned([
            Seq(All("alpha", Seq(Named("Type"), Sp, V("u"))),
                Instance(Call("MeasurableSpace", V("alpha"))),
                All("mu", Call("Measure", V("alpha"))),
                Instance(Call("IsProbabilityMeasure", V("mu")))),
            Seq(All("T", Fn(V("alpha"), V("alpha"))),
                Call("Ergodic", V("T"), V("mu")), Sp, Rightarrow,
                All("g", Fn(V("alpha"), Real)),
                Call("Integrable", V("g"), V("mu")), Sp, Rightarrow),
            ae
        ]));
    }
}
