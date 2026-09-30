import { useEffect } from 'react';
import { coq } from './data/coq';
import { WEB } from './data/refs';
import { useRoute } from './lib/route';
import { EdgesView } from './views/EdgesView';
import { OverviewView } from './views/OverviewView';
import css from './App.module.css';

export function App() {
  const route = useRoute();

  useEffect(() => {
    if (route.view === 'overview') window.scrollTo({ top: 0 });
  }, [route.view]);

  return (
    <div className={css.shell}>
      <nav className={css.bar} aria-label="Primary">
        <a href="#overview" className={css.brand}>
          <span className={css.mark}>⊢</span> WasmCert <span className={css.sub}>proof atlas</span>
        </a>
        <div className={css.tabs} role="tablist">
          <a role="tab" aria-selected={route.view === 'overview'} href="#overview">
            Overview
          </a>
          <a role="tab" aria-selected={route.view === 'edges'} href="#edges">
            Proof edges
          </a>
        </div>
      </nav>

      <main className={css.main}>{route.view === 'overview' ? <OverviewView /> : <EdgesView select={route.select} />}</main>

      <footer className={css.footer}>
        <p>
          Statuses are read from the Coq sources at{' '}
          <a href={`https://github.com/${coq.repo}/tree/${coq.commit}/coq`} target="_blank" rel="noreferrer">
            <code>{coq.repo}@{coq.commit.slice(0, 7)}</code>
          </a>
          {coq.commitDate && <> ({coq.commitDate.slice(0, 10)})</>}: <code>Qed</code> means proved, <code>Admitted</code> and{' '}
          <code>admit</code> mean open. A Qed proof that uses an admitted lemma counts as “relies on admits”.
        </p>
        <p>
          <a href={WEB.report.href} target="_blank" rel="noreferrer">
            {WEB.report.title}
          </a>{' '}
          · by Xuan Huang
        </p>
      </footer>
    </div>
  );
}
