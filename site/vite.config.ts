import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';

// `base: './'` keeps the build relocatable (GitHub Pages project path, artifact previews).
export default defineConfig({
  base: './',
  plugins: [react()],
});
