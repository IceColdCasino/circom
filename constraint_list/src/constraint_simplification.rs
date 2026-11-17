// Uncomment lines 163, 165, 336 and 338 to print cluster information
use super::{ConstraintStorage, EncodingIterator, SEncoded, Simplifier, A, C, S};
use crate::SignalMap;
use circom_algebra::num_bigint::BigInt;
use constraint_writers::json_writer::SubstitutionJSON;
use std::collections::{HashMap, HashSet, LinkedList, BTreeSet};
use std::sync::Arc;

fn log_substitutions(substitutions: &LinkedList<S>, writer: &mut Option<SubstitutionJSON>) {
    use super::json_porting::port_substitution;
    if let Some(w) = writer {
        for s in substitutions {
            let (from, to) = port_substitution(s);
            w.write_substitution(&from, &to).unwrap();
        }
    }
}

#[derive(Default, Clone)]
struct Cluster {
    constraints: LinkedList<C>,
    num_signals: usize
}
impl Cluster {
    pub fn new(constraint: C, num_signals: usize) -> Cluster {
        let mut new = Cluster::default();
        LinkedList::push_back(&mut new.constraints, constraint);
        new.num_signals = num_signals;
        new
    }

    pub fn merge(mut c0: Cluster, mut c1: Cluster) -> Cluster {
        let mut result = Cluster::default();
        LinkedList::append(&mut result.constraints, &mut c0.constraints);
        LinkedList::append(&mut result.constraints, &mut c1.constraints);
        result.num_signals = c0.num_signals + c1.num_signals - 1;
        result
    }

    pub fn size(&self) -> usize {
        LinkedList::len(&self.constraints)
    }
}

fn is_bridge_signal(
    signal: usize,
    forbidden: &HashSet<usize>,
    private_lo: usize,
    private_hi: usize,
) -> bool {
    (private_lo <= signal && signal <= private_hi) || forbidden.contains(&signal)
}

fn build_clusters(linear: LinkedList<C>, no_vars: usize) -> Vec<Cluster> {
    build_clusters_cutting(linear, no_vars, &HashSet::new(), 1, 0)
}

// Signals in `forbidden` and private inputs `[private_lo, private_hi]` are not
// union keys. Chains that only meet at those signals stay separate clusters.
fn build_clusters_cutting(
    linear: LinkedList<C>,
    no_vars: usize,
    forbidden: &HashSet<usize>,
    private_lo: usize,
    private_hi: usize,
) -> Vec<Cluster> {
    type ClusterArena = Vec<Option<Cluster>>;
    type ClusterPath = Vec<usize>;
    fn shrink_jumps_and_find(c_to_c: &mut ClusterPath, org: usize) -> usize {
        let mut current = org;
        let mut jumps = Vec::new();
        while current != c_to_c[current] {
            Vec::push(&mut jumps, current);
            current = c_to_c[current];
        }
        while let Some(redirect) = Vec::pop(&mut jumps) {
            c_to_c[redirect] = current;
        }
        current
    }

    fn arena_merge(arena: &mut ClusterArena, c_to_c: &mut ClusterPath, src: usize, dest: usize) {
        let current_dest = shrink_jumps_and_find(c_to_c, dest);
        let current_src = shrink_jumps_and_find(c_to_c, src);
        let c0 = std::mem::replace(&mut arena[current_dest], None).unwrap_or_default();
        let c1 = std::mem::replace(&mut arena[current_src], None).unwrap_or_default();
        let merged = Cluster::merge(c0, c1);
        arena[current_dest] = Some(merged);
        c_to_c[current_src] = current_dest;
    }

    let no_linear = LinkedList::len(&linear);
    let mut arena = ClusterArena::with_capacity(no_linear);
    let mut cluster_to_current = ClusterPath::with_capacity(no_linear);
    let mut signal_to_cluster = vec![no_linear; no_vars];
    for constraint in linear {
        if !constraint.is_empty(){
            let signals = C::take_cloned_signals(&constraint);
            let dest = ClusterArena::len(&arena);
            ClusterArena::push(&mut arena, Some(Cluster::new(constraint, signals.len())));
            Vec::push(&mut cluster_to_current, dest);
            for signal in signals {
                if is_bridge_signal(signal, forbidden, private_lo, private_hi) {
                    continue;
                }
                let prev = signal_to_cluster[signal];
                signal_to_cluster[signal] = dest;
                if prev < no_linear {
                    arena_merge(&mut arena, &mut cluster_to_current, prev, dest);
                }
            }
        }
    }
    let mut clusters = Vec::new();
    for cluster in arena {
        if let Some(cluster) = cluster {
            if Cluster::size(&cluster) != 0 {
                Vec::push(&mut clusters, cluster);
            }
        }
    }
    clusters
}

fn rebuild_witness(
    max_signal: usize, 
    deleted: &mut HashSet<usize>, 
    forbidden: &HashSet<usize>, 
    non_linear_map: SignalToConstraints, 
    remove_unused: bool,
) -> SignalMap {
    let mut map = SignalMap::with_capacity(max_signal);
    let mut free = LinkedList::new();
    for signal in 0..max_signal {
        if deleted.contains(&signal) {
            free.push_back(signal);
        } else if remove_unused && !forbidden.contains(&signal) && !non_linear_map.contains_key(&signal){
            deleted.insert(signal);
            free.push_back(signal);
        } else if let Some(new_pos) = free.pop_front() {
            map.insert(signal, new_pos);
            free.push_back(signal);
        } else {
            map.insert(signal, signal);
        }
    }
    map
}

fn eq_cluster_simplification(
    mut cluster: Cluster,
    forbidden: &HashSet<usize>,
    field: &BigInt,
) -> (LinkedList<S>, LinkedList<C>) {
    if Cluster::size(&cluster) == 1 {
        let mut substitutions = LinkedList::new();
        let mut constraints = LinkedList::new();
        let constraint = LinkedList::pop_back(&mut cluster.constraints).unwrap();
        let signals: Vec<_> = C::take_cloned_signals_ordered(&constraint).iter().cloned().collect();
        let s_0 = signals[0];
        let s_1 = signals[1];
        if HashSet::contains(forbidden, &s_0) && HashSet::contains(forbidden, &s_1) {
            LinkedList::push_back(&mut constraints, constraint);
        } else if HashSet::contains(forbidden, &s_0) {
            LinkedList::push_back(
                &mut substitutions,
                S::new(s_1, A::Signal { symbol: s_0 }).unwrap(),
            );
        } else if HashSet::contains(forbidden, &s_1) {
            LinkedList::push_back(
                &mut substitutions,
                S::new(s_0, A::Signal { symbol: s_1 }).unwrap(),
            );
        } else {
            let (l, r) = if s_0 > s_1 { (s_0, s_1) } else { (s_1, s_0) };
            LinkedList::push_back(&mut substitutions, S::new(l, A::Signal { symbol: r }).unwrap());
        }
        (substitutions, constraints)
    } else {
        let mut cons = LinkedList::new();
        let mut subs = LinkedList::new();
        let (mut remains, mut min_remains) = (BTreeSet::new(), None);
        let (mut remove, mut min_remove) = (HashSet::new(), None);
        for c in cluster.constraints {
            for signal in C::take_cloned_signals_ordered(&c) {
                if HashSet::contains(&forbidden, &signal) {
                    BTreeSet::insert(&mut remains, signal);
                    min_remains = Some(min_remains.map_or(signal, |s| std::cmp::min(s, signal)));
                } else {
                    min_remove = Some(min_remove.map_or(signal, |s| std::cmp::min(s, signal)));
                    HashSet::insert(&mut remove, signal);
                }
            }
        }

        let rh_signal = if let Some(signal) = min_remains {
            BTreeSet::remove(&mut remains, &signal);
            signal
        } else {
            let signal = min_remove.unwrap();
            HashSet::remove(&mut remove, &signal);
            signal
        };

        for signal in remains {
            let l = A::Signal { symbol: signal };
            let r = A::Signal { symbol: rh_signal };
            let expr = A::sub(&l, &r, field);
            let c = A::transform_expression_to_constraint_form(expr, field).unwrap();
            LinkedList::push_back(&mut cons, c);
        }

        for signal in remove {
            let sub = S::new(signal, A::Signal { symbol: rh_signal }).unwrap();
            LinkedList::push_back(&mut subs, sub);
        }

        (subs, cons)
    }
}

fn eq_simplification(
    equalities: LinkedList<C>,
    forbidden: Arc<HashSet<usize>>,
    no_vars: usize,
    field: &BigInt,
    substitution_log: &mut Option<SubstitutionJSON>,
) -> (LinkedList<S>, LinkedList<C>) {
    use std::sync::mpsc;
    use threadpool::ThreadPool;
    let field = Arc::new(field.clone());
    let mut constraints = LinkedList::new();
    let mut substitutions = LinkedList::new();
    let clusters = build_clusters(equalities, no_vars);
    let (cluster_tx, simplified_rx) = mpsc::channel();
    let pool = ThreadPool::new(num_cpus::get());
    let no_clusters = Vec::len(&clusters);
    // println!("Clusters: {}", no_clusters);
    let mut single_clusters = 0;
    let mut id = 0;
    let mut aux_constraints = vec![LinkedList::new(); clusters.len()];
    for cluster in clusters {
        if Cluster::size(&cluster) == 1 {
            let (mut subs, cons) = eq_cluster_simplification(cluster, &forbidden, &field);
            aux_constraints[id] = cons;
            LinkedList::append(&mut substitutions, &mut subs);
            single_clusters += 1;
        } else {
            let cluster_tx = cluster_tx.clone();
            let forbidden = Arc::clone(&forbidden);
            let field = Arc::clone(&field);
            let job = move || {
                //println!("Cluster: {}", id);
                let result = eq_cluster_simplification(cluster, &forbidden, &field);
                //println!("End of cluster: {}", id);
                cluster_tx.send((id, result)).unwrap();
            };
            ThreadPool::execute(&pool, job);
        }
        let _ = id;
        id += 1;
    }
    // println!("{} clusters were of size 1", single_clusters);
    ThreadPool::join(&pool);
    for _ in 0..(no_clusters - single_clusters) {
        let (id, (mut subs, cons)) = simplified_rx.recv().unwrap();
        aux_constraints[id] = cons;
        LinkedList::append(&mut substitutions, &mut subs);
    }
    for id in 0..no_clusters {
        LinkedList::append(&mut constraints, &mut aux_constraints[id]);
    }
    log_substitutions(&substitutions, substitution_log);
    (substitutions, constraints)
}

fn constant_eq_simplification(
    c_eq: LinkedList<C>,
    forbidden: &HashSet<usize>,
    field: &BigInt,
    substitution_log: &mut Option<SubstitutionJSON>,
) -> (LinkedList<S>, LinkedList<C>) {
    let mut cons = LinkedList::new();
    let mut subs = LinkedList::new();
    for constraint in c_eq {
        let mut signals: Vec<_> = C::take_cloned_signals_ordered(&constraint).iter().cloned().collect();
        let signal = signals.pop().unwrap();
        if HashSet::contains(&forbidden, &signal) {
            LinkedList::push_back(&mut cons, constraint);
        } else {
            let sub = C::clear_signal_from_linear(constraint, &signal, field);
            LinkedList::push_back(&mut subs, sub);
        }
    }
    log_substitutions(&subs, substitution_log);
    (subs, cons)
}

fn forbid_private_inputs(
    forbidden: &HashSet<usize>,
    linear: &LinkedList<C>,
    private_lo: usize,
    private_hi: usize,
) -> HashSet<usize> {
    let mut extended = forbidden.clone();
    if private_lo > private_hi {
        return extended;
    }
    for constraint in linear {
        for signal in C::take_cloned_signals(constraint) {
            if private_lo <= signal && signal <= private_hi {
                extended.insert(signal);
            }
        }
    }
    extended
}

fn compose_substitutions(earlier: &mut LinkedList<S>, later: &LinkedList<S>, field: &BigInt) {
    use circom_algebra::simplification_utils::build_encoded_fast_substitutions;
    use circom_algebra::simplification_utils::fast_encoded_substitution_substitution;
    if earlier.is_empty() || later.is_empty() {
        return;
    }
    let mut copy = LinkedList::new();
    for substitution in later {
        copy.push_back(substitution.clone());
    }
    let encoded = build_encoded_fast_substitutions(copy);
    for substitution in earlier.iter_mut() {
        fast_encoded_substitution_substitution(substitution, &encoded, field);
    }
}

fn simplify_clusters(
    clusters: Vec<Cluster>,
    forbidden: Arc<HashSet<usize>>,
    field: &BigInt,
    use_old_heuristics: bool,
) -> (LinkedList<S>, LinkedList<C>) {
    use circom_algebra::simplification_utils::full_simplification;
    use circom_algebra::simplification_utils::Config;
    use circom_algebra::simplification_utils::Simplified;
    use std::sync::mpsc;
    use threadpool::ThreadPool;

    fn run_cluster(
        cluster: Cluster,
        forbidden: Arc<HashSet<usize>>,
        field: &BigInt,
        use_old_heuristics: bool,
    ) -> Simplified {
        full_simplification(Config {
            field: field.clone(),
            constraints: cluster.constraints,
            forbidden,
            num_signals: cluster.num_signals,
            use_old_heuristics,
        })
    }

    let mut small = Vec::new();
    let mut large = Vec::new();
    for cluster in clusters {
        if Cluster::size(&cluster) <= 1 {
            small.push(cluster);
        } else {
            large.push(cluster);
        }
    }

    let (tx, rx) = mpsc::channel();
    let mut jobs = 0;
    let mut pool = None;
    let mut batch = Vec::new();
    for cluster in small {
        batch.push(cluster);
        if batch.len() == 1024 {
            jobs += 1;
            let tx = tx.clone();
            let forbidden = Arc::clone(&forbidden);
            let field = field.clone();
            let pool = pool.get_or_insert_with(|| ThreadPool::new(num_cpus::get()));
            let batch = std::mem::take(&mut batch);
            ThreadPool::execute(pool, move || {
                let mut out = Vec::with_capacity(batch.len());
                for cluster in batch {
                    out.push(run_cluster(cluster, Arc::clone(&forbidden), &field, use_old_heuristics));
                }
                tx.send(out).unwrap();
            });
        }
    }
    if !batch.is_empty() {
        jobs += 1;
        let tx = tx.clone();
        let forbidden = Arc::clone(&forbidden);
        let field = field.clone();
        let pool = pool.get_or_insert_with(|| ThreadPool::new(num_cpus::get()));
        ThreadPool::execute(pool, move || {
            let mut out = Vec::with_capacity(batch.len());
            for cluster in batch {
                out.push(run_cluster(cluster, Arc::clone(&forbidden), &field, use_old_heuristics));
            }
            tx.send(out).unwrap();
        });
    }
    for cluster in large {
        jobs += 1;
        let tx = tx.clone();
        let forbidden = Arc::clone(&forbidden);
        let field = field.clone();
        let pool = pool.get_or_insert_with(|| ThreadPool::new(num_cpus::get()));
        ThreadPool::execute(pool, move || {
            tx.send(vec![run_cluster(cluster, forbidden, &field, use_old_heuristics)]).unwrap();
        });
    }
    drop(tx);
    if let Some(pool) = pool {
        ThreadPool::join(&pool);
    }

    let mut cons = LinkedList::new();
    let mut substitutions = LinkedList::new();
    for _ in 0..jobs {
        for mut result in rx.recv().unwrap() {
            LinkedList::append(&mut cons, &mut result.constraints);
            LinkedList::append(&mut substitutions, &mut result.substitutions);
        }
    }
    (substitutions, cons)
}

fn linear_simplification(
    log: &mut Option<SubstitutionJSON>,
    linear: LinkedList<C>,
    forbidden: Arc<HashSet<usize>>,
    no_labels: usize,
    field: &BigInt,
    use_old_heuristics: bool,
    private_lo: usize,
    private_hi: usize,
) -> (LinkedList<S>, LinkedList<C>) {
    // Chains that only share private inputs or public signals are independent.
    // Simplify them in parallel, then simplify the residuals together so those
    // inputs can still be removed.
    let phase1_forbidden = Arc::new(forbid_private_inputs(&forbidden, &linear, private_lo, private_hi));
    let clusters = build_clusters_cutting(linear, no_labels, &forbidden, private_lo, private_hi);
    let (mut substitutions, residuals) =
        simplify_clusters(clusters, Arc::clone(&phase1_forbidden), field, use_old_heuristics);
    let mut residuals_kept = LinkedList::new();
    for constraint in residuals {
        if !C::is_empty(&constraint) {
            residuals_kept.push_back(constraint);
        }
    }
    let residual_clusters = build_clusters(residuals_kept, no_labels);
    let (mut residual_substitutions, mut cons) =
        simplify_clusters(residual_clusters, forbidden, field, use_old_heuristics);
    compose_substitutions(&mut substitutions, &residual_substitutions, field);
    LinkedList::append(&mut substitutions, &mut residual_substitutions);
    let mut kept = LinkedList::new();
    for constraint in cons {
        if !C::is_empty(&constraint) {
            kept.push_back(constraint);
        }
    }
    cons = kept;
    log_substitutions(&substitutions, log);
    (substitutions, cons)
}

type SignalToConstraints = HashMap<usize, LinkedList<usize>>;
fn build_non_linear_signal_map(non_linear: &ConstraintStorage) -> SignalToConstraints {
    let mut map = SignalToConstraints::new();
    for c_id in non_linear.get_ids() {
        let constraint = non_linear.read_constraint(c_id).unwrap();
        for signal in C::take_cloned_signals(&constraint) {
            if let Some(list) = map.get_mut(&signal) {
                list.push_back(c_id);
            } else {
                let mut new = LinkedList::new();
                new.push_back(c_id);
                map.insert(signal, new);
            }
        }
    }
    map
}

fn apply_substitution_to_map(
    storage: &mut ConstraintStorage,
    map: &mut SignalToConstraints,
    substitutions: &LinkedList<S>,
    field: &BigInt,
) -> LinkedList<C> {
    fn constraint_processing(
        storage: &mut ConstraintStorage,
        map: &mut SignalToConstraints,
        c_ids: &LinkedList<usize>,
        substitution: &S,
        field: &BigInt,
    ) -> LinkedList<usize> {
        let mut linear = LinkedList::new();
        let signals: LinkedList<_> = substitution.to().keys().cloned().collect();
        for c_id in c_ids {
            let c_id = *c_id;
            let mut constraint = storage.read_constraint(c_id).unwrap();
            C::apply_substitution(&mut constraint, substitution, field);
            C::fix_constraint(&mut constraint, field);
            if C::is_linear(&constraint) {
                linear.push_back(c_id);
            }
            storage.replace(c_id, constraint);
            for signal in &signals {
                if let Some(list) = map.get_mut(&signal) {
                    list.push_back(c_id);
                } else {
                    let mut new = LinkedList::new();
                    new.push_back(c_id);
                    map.insert(*signal, new);
                }
            }
        }
        linear
    }

    let mut linear_id = LinkedList::new();
    for substitution in substitutions {
        if let Some(c_ids) = map.get(substitution.from()).cloned() {
            let mut new_linear = constraint_processing(storage, map, &c_ids, substitution, field);
            linear_id.append(&mut new_linear);
        }
    }
    let mut linear = LinkedList::new();
    for c_id in linear_id {
        let constraint = storage.read_constraint(c_id).unwrap();
        linear.push_back(constraint);
        storage.replace(c_id, C::empty());
    }
    linear
}

fn build_relevant_set(
    mut iter: EncodingIterator,
    relevant: &mut HashSet<usize>,
    renames: &SEncoded,
    deletes: &SEncoded,
) {
    fn unwrapped_signal(map: &SEncoded, signal: usize) -> Option<usize> {
        let f = |e: &A| {
            if let A::Signal { symbol } = e {
                Some(*symbol)
            } else {
                None
            }
        };
        SEncoded::get(map, &signal).map_or(None, f)
    }

    let (_, non_linear) = EncodingIterator::take(&mut iter);
    for c in non_linear {
        for signal in C::take_cloned_signals(&c) {
            let signal = unwrapped_signal(renames, signal).unwrap_or(signal);
            if !SEncoded::contains_key(deletes, &signal) {
                HashSet::insert(relevant, signal);
            }
        }
    }

    for edge in EncodingIterator::edges(&iter) {
        let next = EncodingIterator::next(&iter, edge);
        build_relevant_set(next, relevant, renames, deletes)
    }
}

fn remove_not_relevant(substitutions: &mut SEncoded, relevant: &HashSet<usize>) {
    let signals: Vec<_> = substitutions.keys().cloned().collect();
    for signal in signals {
        if !HashSet::contains(&relevant, &signal) {
            SEncoded::remove(substitutions, &signal);
        }
    }
}


// returns the constraints, the assignment of the witness and the number of inputs in the witness
pub fn simplification(smp: &mut Simplifier) -> (ConstraintStorage, SignalMap, usize) {
    use super::non_linear_utils::obtain_and_simplify_non_linear;
    use circom_algebra::simplification_utils::build_encoded_fast_substitutions;
    use circom_algebra::simplification_utils::fast_encoded_constraint_substitution;
    use std::time::SystemTime;

    let mut substitution_log =
        if smp.port_substitution { 
            Some(SubstitutionJSON::new(&smp.json_substitutions).unwrap()) 
        } else {
             None 
        };
    let apply_linear = !smp.flag_s;
    let use_old_heuristics = smp.flag_old_heuristics;
    let field = smp.field.clone();
    let forbidden = Arc::new(std::mem::replace(&mut smp.forbidden, HashSet::with_capacity(0)));
    let no_labels = Simplifier::no_labels(smp);
    let equalities = std::mem::replace(&mut smp.equalities, LinkedList::new());
    let max_signal = smp.max_signal;
    let mut cons_equalities = std::mem::replace(&mut smp.cons_equalities, LinkedList::new());
    let mut linear = std::mem::replace(&mut smp.linear, LinkedList::new());
    let mut deleted = HashSet::new();
    let mut lconst = LinkedList::new();
    let mut no_rounds = smp.no_rounds;
    let remove_unused = true;
    let private_lo = smp.no_public_outputs + smp.no_public_inputs + 1;
    let private_hi = smp.no_public_outputs + smp.no_public_inputs + smp.no_private_inputs;

    let relevant_signals = {
        // println!("Creating first relevant set");
        let now = SystemTime::now();
        let mut relevant = HashSet::new();
        let iter = EncodingIterator::new(&smp.dag_encoding);
        let s_sub = HashMap::with_capacity(0);
        let c_sub = HashMap::with_capacity(0);
        build_relevant_set(iter, &mut relevant, &s_sub, &c_sub);
        let _dur = now.elapsed().unwrap_or_default().as_millis();
        // println!("First relevant set created: {} ms", dur);
        relevant
    };

    let single_substitutions = {
        // println!("Start of single assignment simplification");
        let now = SystemTime::now();
        let (subs, mut cons) = eq_simplification(
            equalities,
            Arc::clone(&forbidden),
            no_labels,
            &field,
            &mut substitution_log,
        );

        LinkedList::append(&mut lconst, &mut cons);
        let mut substitutions = build_encoded_fast_substitutions(subs);
        for constraint in &mut linear {
            if fast_encoded_constraint_substitution(constraint, &substitutions, &field){
                C::fix_constraint(constraint, &field);
            }
        }
        for constraint in &mut cons_equalities {
            if fast_encoded_constraint_substitution(constraint, &substitutions, &field){
                C::fix_constraint(constraint, &field);
            }
        }
        for signal in substitutions.keys().cloned() {
            deleted.insert(signal);
        }
        remove_not_relevant(&mut substitutions, &relevant_signals);
        let _dur = now.elapsed().unwrap_or_default().as_millis();
        // println!("End of single assignment simplification: {} ms", dur);
        substitutions
    };

    let cons_substitutions = {
        // println!("Start of constant assignment simplification");
        let now = SystemTime::now();
        let (subs, mut cons) =
            constant_eq_simplification(cons_equalities, &forbidden, &field, &mut substitution_log);
        LinkedList::append(&mut lconst, &mut cons);
        let substitutions = build_encoded_fast_substitutions(subs);
        for constraint in &mut linear {
            if fast_encoded_constraint_substitution(constraint, &substitutions, &field){
                C::fix_constraint(constraint, &field);
            }
        }
        for signal in substitutions.keys().cloned() {
            deleted.insert(signal);
        }
        let _dur = now.elapsed().unwrap_or_default().as_millis();
        // println!("End of constant assignment simplification: {} ms", dur);
        substitutions
    };

    let relevant_signals = {
        // println!("Start building relevant");
        let now = SystemTime::now();
        let mut relevant = HashSet::new();
        let iter = EncodingIterator::new(&smp.dag_encoding);
        build_relevant_set(iter, &mut relevant, &single_substitutions, &cons_substitutions);
        let _dur = now.elapsed().unwrap_or_default().as_millis();
        // println!("Relevant built: {} ms", dur);
        relevant
    };

    let linear_substitutions = if apply_linear {
        let now = SystemTime::now();
        let (subs, mut cons) = linear_simplification(
            &mut substitution_log,
            linear,
            Arc::clone(&forbidden),
            no_labels,
            &field,
            use_old_heuristics,
            private_lo,
            private_hi,
        );
        // println!("Building substitution map");
        let now0 = SystemTime::now();
        let mut only_relevant = LinkedList::new();
        for substitution in subs {
            deleted.insert(*substitution.from());
            if relevant_signals.contains(substitution.from()) {
                only_relevant.push_back(substitution);
            }
        }
        let substitutions = build_encoded_fast_substitutions(only_relevant);
        let _dur0 = now0.elapsed().unwrap_or_default().as_millis();
        // println!("End of substitution map: {} ms", dur0);
        let _dur = now.elapsed().unwrap_or_default().as_millis();
        // println!("End of cluster simplification: {} ms", dur);
        LinkedList::append(&mut lconst, &mut cons);
        for constraint in &mut lconst {
            if fast_encoded_constraint_substitution(constraint, &substitutions, &field){
                C::fix_constraint(constraint, &field);
            }
        }
        substitutions
    } else {
        LinkedList::append(&mut lconst, &mut linear);
        HashMap::with_capacity(0)
    };

    let (with_linear, mut constraint_storage) = {
        // println!("Building constraint storage");
        let now = SystemTime::now();
        let mut frames = LinkedList::new();
        LinkedList::push_back(&mut frames, single_substitutions);
        LinkedList::push_back(&mut frames, cons_substitutions);
        LinkedList::push_back(&mut frames, linear_substitutions);
        let iter = EncodingIterator::new(&smp.dag_encoding);
        let mut storage = ConstraintStorage::new();
        let with_linear = obtain_and_simplify_non_linear(iter, &mut storage, &frames, &field);
        crate::state_utils::empty_encoding_constraints(&mut smp.dag_encoding);
        let _dur = now.elapsed().unwrap_or_default().as_millis();
        // println!("Storages built in {} ms", dur);
        if no_rounds > 0{
            no_rounds -= 1;
        }
        (with_linear, storage)
    };

    let mut round_id = 0;
    let _ = round_id;
    let mut linear = with_linear;
    let mut apply_round = apply_linear && no_rounds > 0 && !linear.is_empty();
    let mut non_linear_map = if apply_round || remove_unused {
        // println!("Building non-linear map");
        let now = SystemTime::now();
        let non_linear_map = build_non_linear_signal_map(&constraint_storage);
        let _dur = now.elapsed().unwrap_or_default().as_millis();
        // println!("Non-linear was built in {} ms", dur);
        non_linear_map
    } else {
        SignalToConstraints::with_capacity(0)
    };
    while apply_round {
        let now = SystemTime::now();
        // println!("Number of linear constraints: {}", linear.len());
        let (substitutions, mut constants) = linear_simplification(
            &mut substitution_log,
            linear,
            Arc::clone(&forbidden),
            no_labels,
            &field,
            use_old_heuristics,
            private_lo,
            private_hi,
        );

        for sub in &substitutions {
            deleted.insert(*sub.from());
        }
        lconst.append(&mut constants);
        for constraint in &mut lconst {
            for substitution in &substitutions {
                C::apply_substitution(constraint, substitution, &field);
            }
            C::fix_constraint(constraint, &field);
        }
        linear = apply_substitution_to_map(
            &mut constraint_storage,
            &mut non_linear_map,
            &substitutions,
            &field,
        );
        round_id += 1;
        no_rounds -= 1;
        apply_round = !linear.is_empty() && no_rounds > 0;
        let _dur = now.elapsed().unwrap_or_default().as_millis();
        // println!("Iteration no {} took {} ms", round_id, dur);
    }

    for constraint in linear {
        if remove_unused {
            let signals =  C::take_cloned_signals(&constraint);
            let c_id = constraint_storage.add_constraint(constraint);
            for signal in signals {
                if let Some(list) = non_linear_map.get_mut(&signal) {
                    list.push_back(c_id);
                } else {
                    let mut new = LinkedList::new();
                    new.push_back(c_id);
                    non_linear_map.insert(signal, new);
                }
            }
        }
        else{
            constraint_storage.add_constraint(constraint);
        }
    }
    for mut constraint in lconst {
        if remove_unused{
            C::fix_constraint(&mut constraint, &field);
            let signals =  C::take_cloned_signals(&constraint);
            let c_id = constraint_storage.add_constraint(constraint);
            for signal in signals {
                if let Some(list) = non_linear_map.get_mut(&signal) {
                    list.push_back(c_id);
                } else {
                    let mut new = LinkedList::new();
                    new.push_back(c_id);
                    non_linear_map.insert(signal, new);
                }
            }
        }
        else{
            C::fix_constraint(&mut constraint, &field);
            constraint_storage.add_constraint(constraint);
        }
    }

    let erased = crate::non_linear_simplification::simplify(
        &mut constraint_storage,
        &forbidden,
        &field
    );

    for signal in erased {
        deleted.insert(signal);
    }

    let _trash = constraint_storage.extract_with(&|c| C::is_empty(c));


    let signal_map = {
        // println!("Rebuild witness");
        let now = SystemTime::now();
        let signal_map= rebuild_witness(
            max_signal, 
            &mut deleted, 
            &forbidden, 
            non_linear_map, 
            remove_unused
        );
        let _dur = now.elapsed().unwrap_or_default().as_millis();
        // println!("End of rebuild witness: {} ms", dur);
       signal_map
    };

    // count the number of deleted inputs
    let max_value_input = smp.no_public_outputs + smp.no_public_inputs + smp.no_private_inputs;
    let mut deleted_inputs = 0;
    for signal in &deleted{
        if signal >= &(smp.no_public_outputs + 1) && signal <= &max_value_input{
            deleted_inputs += 1;
        }
    }


    if let Some(w) = substitution_log {
        w.end().unwrap();
    }
    // println!("NO CONSTANTS: {}", constraint_storage.no_constants());
    (constraint_storage, signal_map, smp.no_private_inputs - deleted_inputs)
}

#[cfg(test)]
mod tests {
    use super::{
        build_clusters, build_clusters_cutting, linear_simplification, simplify_clusters, A, C, S,
    };
    use circom_algebra::modular_arithmetic;
    use circom_algebra::num_bigint::BigInt;
    use circom_algebra::num_traits::Zero;
    use std::collections::{BTreeSet, HashMap, HashSet, LinkedList};
    use std::sync::Arc;

    fn linear_constraint(terms: &[(usize, i64)], field: &BigInt) -> C {
        let mut coefficients = HashMap::new();
        coefficients.insert(0usize, BigInt::from(0));
        for &(signal, coef) in terms {
            coefficients.insert(signal, BigInt::from(coef));
        }
        let mut constraint =
            A::transform_expression_to_constraint_form(A::Linear { coefficients }, field).unwrap();
        C::remove_zero_value_coefficients(&mut constraint);
        constraint
    }

    fn push(constraints: &mut LinkedList<C>, terms: &[(usize, i64)], field: &BigInt) {
        constraints.push_back(linear_constraint(terms, field));
    }

    /// Row/column prefix sums and bit packing, all glued together by a private
    /// permutation matrix. Mirrors the 8-deck linear system at a smaller n.
    fn permutation_system(n: usize, field: &BigInt) -> (LinkedList<C>, usize, usize, usize) {
        let private_lo = 1usize;
        let private_hi = n * n;
        let mut next = private_hi + 1;
        let mut constraints = LinkedList::new();
        let p = |i: usize, j: usize| private_lo + i * n + j;

        for i in 0..n {
            let mut prev = None;
            for j in 0..n {
                let acc = next;
                next += 1;
                let bit = p(i, j);
                if let Some(prev) = prev {
                    push(&mut constraints, &[(acc, 1), (prev, -1), (bit, -1)], field);
                } else {
                    push(&mut constraints, &[(acc, 1), (bit, -1)], field);
                }
                prev = Some(acc);
            }
            push(&mut constraints, &[(prev.unwrap(), 1), (0, -1)], field);
        }
        for j in 0..n {
            let mut prev = None;
            for i in 0..n {
                let acc = next;
                next += 1;
                let bit = p(i, j);
                if let Some(prev) = prev {
                    push(&mut constraints, &[(acc, 1), (prev, -1), (bit, -1)], field);
                } else {
                    push(&mut constraints, &[(acc, 1), (bit, -1)], field);
                }
                prev = Some(acc);
            }
            push(&mut constraints, &[(prev.unwrap(), 1), (0, -1)], field);
        }
        for i in 0..n {
            let mut prev = None;
            for j in 0..n {
                let acc = next;
                next += 1;
                let bit = p(i, j);
                if let Some(prev) = prev {
                    push(&mut constraints, &[(acc, 1), (prev, -2), (bit, -1)], field);
                } else {
                    push(&mut constraints, &[(acc, 1), (bit, -1)], field);
                }
                prev = Some(acc);
            }
        }
        for i in 0..n {
            for j in 0..n {
                let diff = next;
                next += 1;
                push(&mut constraints, &[(diff, 1), (p(i, j), -1), (0, 1)], field);
            }
        }
        (constraints, next, private_lo, private_hi)
    }

    fn constraint_row(constraint: &C) -> HashMap<usize, BigInt> {
        constraint.c().clone()
    }

    fn substitution_row(substitution: &S, field: &BigInt) -> HashMap<usize, BigInt> {
        constraint_row(&S::substitution_into_constraint(substitution.clone(), field))
    }

    fn normalize(value: &BigInt, field: &BigInt) -> BigInt {
        modular_arithmetic::add(value, &BigInt::from(0), field)
    }

    fn sub_scaled(
        row: &mut HashMap<usize, BigInt>,
        pivot: &HashMap<usize, BigInt>,
        coef: &BigInt,
        field: &BigInt,
    ) {
        for (signal, value) in pivot {
            let product = modular_arithmetic::mul(coef, value, field);
            let current = row.get(signal).cloned().unwrap_or_else(|| BigInt::from(0));
            let next = modular_arithmetic::sub(&current, &product, field);
            if next.is_zero() {
                row.remove(signal);
            } else {
                row.insert(*signal, next);
            }
        }
    }

    fn rref(mut rows: Vec<HashMap<usize, BigInt>>, field: &BigInt) -> Vec<(usize, HashMap<usize, BigInt>)> {
        let mut columns = BTreeSet::new();
        for row in &rows {
            for signal in row.keys() {
                columns.insert(*signal);
            }
        }
        let mut rank_rows = Vec::new();
        let mut cursor = 0;
        for column in columns {
            let mut pivot_at = None;
            for index in cursor..rows.len() {
                if rows[index]
                    .get(&column)
                    .map(|value| !normalize(value, field).is_zero())
                    .unwrap_or(false)
                {
                    pivot_at = Some(index);
                    break;
                }
            }
            let Some(pivot_at) = pivot_at else { continue };
            rows.swap(cursor, pivot_at);
            let pivot_coef = normalize(&rows[cursor][&column], field);
            let inv = modular_arithmetic::div(&BigInt::from(1), &pivot_coef, field)
                .unwrap_or_else(|_| panic!("pivot coefficient has no inverse"));
            let keys: Vec<usize> = rows[cursor].keys().cloned().collect();
            for key in keys {
                let next = modular_arithmetic::mul(&rows[cursor][&key], &inv, field);
                if next.is_zero() {
                    rows[cursor].remove(&key);
                } else {
                    rows[cursor].insert(key, next);
                }
            }
            let pivot = rows[cursor].clone();
            for index in 0..rows.len() {
                if index == cursor {
                    continue;
                }
                if let Some(coef) = rows[index].get(&column).cloned() {
                    if !normalize(&coef, field).is_zero() {
                        let mut row = std::mem::take(&mut rows[index]);
                        sub_scaled(&mut row, &pivot, &coef, field);
                        rows[index] = row;
                    }
                }
            }
            rank_rows.push((column, pivot));
            cursor += 1;
        }
        rank_rows
    }

    fn assert_same_span(
        original: &LinkedList<C>,
        reduced: &(LinkedList<S>, LinkedList<C>),
        field: &BigInt,
    ) {
        let original_rows: Vec<_> = original.iter().map(constraint_row).collect();
        let mut reduced_rows = Vec::new();
        for substitution in &reduced.0 {
            reduced_rows.push(substitution_row(substitution, field));
        }
        for constraint in &reduced.1 {
            reduced_rows.push(constraint_row(constraint));
        }
        let original_rref = rref(original_rows, field);
        let reduced_rank = rref(reduced_rows.clone(), field).len();
        assert_eq!(
            reduced_rank,
            original_rref.len(),
            "reduced system rank {reduced_rank} != original rank {}",
            original_rref.len()
        );
        for mut row in reduced_rows {
            for (pivot_col, pivot) in &original_rref {
                if let Some(coef) = row.get(pivot_col).cloned() {
                    if !normalize(&coef, field).is_zero() {
                        sub_scaled(&mut row, pivot, &coef, field);
                    }
                }
            }
            let leftover: Vec<_> = row
                .iter()
                .filter(|(_, value)| !normalize(value, field).is_zero())
                .map(|(signal, value)| (*signal, value.clone()))
                .collect();
            assert!(
                leftover.is_empty(),
                "reduced equation is not implied by the original system: {:?}",
                leftover
            );
        }
    }

    #[test]
    fn private_input_bridges_split_without_changing_the_linear_span() {
        let n = 4;
        let field = BigInt::from(101);
        let (constraints, n_signals, private_lo, private_hi) = permutation_system(n, &field);
        let mut forbidden = HashSet::new();
        forbidden.insert(0);
        let forbidden = Arc::new(forbidden);

        let uncut = build_clusters(constraints.clone(), n_signals);
        assert_eq!(uncut.len(), 1, "shared private inputs must form one cluster");
        let cut = build_clusters_cutting(
            constraints.clone(),
            n_signals,
            &forbidden,
            private_lo,
            private_hi,
        );
        assert!(
            cut.len() >= 3 * n,
            "chains should split across private inputs, got {} clusters",
            cut.len()
        );

        let monolithic = simplify_clusters(uncut, Arc::clone(&forbidden), &field, false);
        let split = linear_simplification(
            &mut None,
            constraints.clone(),
            forbidden,
            n_signals,
            &field,
            false,
            private_lo,
            private_hi,
        );
        assert_same_span(&constraints, &monolithic, &field);
        assert_same_span(&constraints, &split, &field);
        assert_nonoverlapping(&split.0);
    }

    #[test]
    fn private_input_does_not_merge_independent_chains() {
        let field = BigInt::from(101);
        let mut constraints = LinkedList::new();
        // Signal 1 is a private input. Each chain otherwise uses its own accumulators.
        push(&mut constraints, &[(2, 1), (1, -1)], &field);
        push(&mut constraints, &[(3, 1), (2, -1)], &field);
        push(&mut constraints, &[(4, 1), (1, -1)], &field);
        push(&mut constraints, &[(5, 1), (4, -1)], &field);
        let n_signals = 6;
        let mut forbidden = HashSet::new();
        forbidden.insert(0);
        let forbidden = Arc::new(forbidden);

        let uncut = build_clusters(constraints.clone(), n_signals);
        assert_eq!(uncut.len(), 1);
        let cut = build_clusters_cutting(constraints.clone(), n_signals, &forbidden, 1, 1);
        assert_eq!(cut.len(), 2, "the private input must not glue the two chains");

        let split = linear_simplification(
            &mut None,
            constraints.clone(),
            forbidden,
            n_signals,
            &field,
            false,
            1,
            1,
        );
        assert_same_span(&constraints, &split, &field);
        assert_nonoverlapping(&split.0);
    }

    #[test]
    fn no_private_inputs_preserves_linear_span() {
        let field = BigInt::from(101);
        let mut constraints = LinkedList::new();
        push(&mut constraints, &[(2, 1), (1, -1)], &field);
        push(&mut constraints, &[(3, 1), (2, -1), (0, -1)], &field);
        push(&mut constraints, &[(4, 1), (3, -1)], &field);
        push(&mut constraints, &[(4, 1), (1, -1), (0, -1)], &field);
        let n_signals = 5;
        let mut forbidden = HashSet::new();
        forbidden.insert(0);
        let forbidden = Arc::new(forbidden);

        let uncut = build_clusters(constraints.clone(), n_signals);
        assert_eq!(uncut.len(), 1);
        let monolithic = simplify_clusters(uncut, Arc::clone(&forbidden), &field, false);
        let split = linear_simplification(
            &mut None,
            constraints.clone(),
            forbidden,
            n_signals,
            &field,
            false,
            1,
            0,
        );
        assert_same_span(&constraints, &monolithic, &field);
        assert_same_span(&constraints, &split, &field);
        assert_nonoverlapping(&split.0);
    }

    #[test]
    fn forbidden_public_signal_is_not_eliminated() {
        let field = BigInt::from(101);
        let mut constraints = LinkedList::new();
        // Signal 1 is a public output. Signal 2 is an intermediate.
        push(&mut constraints, &[(2, 1), (1, -1)], &field);
        push(&mut constraints, &[(2, 1), (0, -1)], &field);
        let n_signals = 3;
        let mut forbidden = HashSet::new();
        forbidden.insert(0);
        forbidden.insert(1);
        let forbidden = Arc::new(forbidden);

        let split = linear_simplification(
            &mut None,
            constraints.clone(),
            Arc::clone(&forbidden),
            n_signals,
            &field,
            false,
            1,
            0,
        );
        assert_same_span(&constraints, &split, &field);
        assert_nonoverlapping(&split.0);
        for substitution in &split.0 {
            assert!(
                !forbidden.contains(substitution.from()),
                "eliminated forbidden signal {}",
                substitution.from()
            );
        }
    }

    fn assert_nonoverlapping(substitutions: &LinkedList<S>) {
        let mut eliminated = HashSet::new();
        for substitution in substitutions {
            assert!(
                eliminated.insert(*substitution.from()),
                "signal {} was eliminated twice",
                substitution.from()
            );
        }
        for substitution in substitutions {
            for signal in substitution.to().keys() {
                assert!(
                    !eliminated.contains(signal),
                    "substitution for {} still mentions eliminated signal {}",
                    substitution.from(),
                    signal
                );
            }
        }
    }
}



