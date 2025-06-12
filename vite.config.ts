import { defineConfig } from 'vite'

export default defineConfig({
  test: {
    globals: true,
    environment: 'node',
  },
  optimizeDeps: {
    exclude: ['@rdfjs/types']
  }
})
