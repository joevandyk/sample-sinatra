listen 8080
worker_processes 3
preload_app true

if GC.respond_to?(:copy_on_write_friendly=)
  GC.copy_on_write_friendly = true
end
